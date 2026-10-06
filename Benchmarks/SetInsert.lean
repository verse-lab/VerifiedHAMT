import VerifiedHAMT

/-! Paired native-code insertion measurements. Each round starts from the same
borrowed seed, consumes successive maps, and optionally retains every old map.
Completed rounds are observed and released inside the timed batch. -/

namespace VerifiedHAMT.SetInsertBenchmarks

private structure RoundResult (α : Type) [BEq α] [Hashable α] where
  finalSet : Lean.PersistentHashSet α
  history : Array (Lean.PersistentHashSet α)

-- Identical insertion loops with cyclically rotated operation order. The round
-- number changes the start position, so a pure result cannot be hoisted out of
-- the batch loop. Two ranges avoid per-operation modular arithmetic.
@[noinline] private def nativeRound [BEq α] [Hashable α]
    (seed : @& Lean.PersistentHashSet α) (ops : @& Array α)
    (retain : Bool) (start : Nat) : RoundResult α := Id.run do
  let mut set := seed
  let mut history := #[]
  for h : i in [start:ops.size] do
    if retain then history := history.push set
    set := Lean.PersistentHashSet.insert set ops[i]
  for i in [0:start] do
    if h : i < ops.size then
      if retain then history := history.push set
      set := Lean.PersistentHashSet.insert set ops[i]
  return ⟨set, history⟩

@[noinline] private def totalRound [BEq α] [LawfulBEq α] [Hashable α]
    (seed : @& VerifiedHAMT.Set α) (ops : @& Array α)
    (retain : Bool) (start : Nat) : RoundResult α := Id.run do
  let mut set := seed
  let mut history := #[]
  for h : i in [start:ops.size] do
    if retain then history := history.push set.toRaw
    set := VerifiedHAMT.Set.insert set ops[i]
  for i in [0:start] do
    if h : i < ops.size then
      if retain then history := history.push set.toRaw
      set := VerifiedHAMT.Set.insert set ops[i]
  return ⟨set.toRaw, history⟩

-- Common observation code: check the last inserted key in the final set and in
-- a retained snapshot. In snapshot workloads that key is new and must be absent
-- from every old snapshot. Destruction of the result/history is timed too.
@[noinline] private def digest [BEq α] [Hashable α]
    (result : RoundResult α) (probe : α) : UInt64 :=
  let last := if result.finalSet.contains probe then 1 else 0
  let old := if h : result.history.size > 0 then
      if result.history[result.history.size / 2].contains probe then 1 else 0
    else 0
  (last + old + result.history.size).toUInt64

@[noinline] private def nativeBatch [BEq α] [Hashable α]
    (seed : @& Lean.PersistentHashSet α) (ops : @& Array α)
    (retain : Bool) (rounds : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for round in [0:rounds] do
    let start := round % ops.size
    let last := if start == 0 then ops.size - 1 else start - 1
    if h : last < ops.size then
      checksum := checksum + digest (nativeRound seed ops retain start) ops[last]
  return checksum

@[noinline] private def totalBatch [BEq α] [LawfulBEq α] [Hashable α]
    (seed : @& VerifiedHAMT.Set α) (ops : @& Array α)
    (retain : Bool) (rounds : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for round in [0:rounds] do
    let start := round % ops.size
    let last := if start == 0 then ops.size - 1 else start - 1
    if h : last < ops.size then
      checksum := checksum + digest (totalRound seed ops retain start) ops[last]
  return checksum

private structure Measurement where
  nanos : Nat
  checksum : UInt64

private def measureNative [BEq α] [Hashable α]
    (seed : Lean.PersistentHashSet α) (ops : Array α)
    (retain : Bool) (rounds : Nat) : IO Measurement := do
  let start ← IO.monoNanosNow
  let checksum := nativeBatch seed ops retain rounds
  Runtime.hold checksum
  let stop ← IO.monoNanosNow
  return ⟨stop - start, checksum⟩

private def measureTotal [BEq α] [LawfulBEq α] [Hashable α]
    (seed : VerifiedHAMT.Set α) (ops : Array α)
    (retain : Bool) (rounds : Nat) : IO Measurement := do
  let start ← IO.monoNanosNow
  let checksum := totalBatch seed ops retain rounds
  Runtime.hold checksum
  let stop ← IO.monoNanosNow
  return ⟨stop - start, checksum⟩

private def shuffledIds (count : Nat) : Array Nat := Id.run do
  let mut ids := (List.range count).toArray
  let mut state : UInt64 := 20261001
  for i in [0:count] do
    state := state * 6364136223846793005 + 1442695040888963407
    let j := i + (state >>> 32).toNat % (count - i)
    ids := ids.swapIfInBounds i j
  return ids

private def validate [BEq α] [Hashable α] (label : String) (makeKey : Nat → α)
    (baseSize : Nat) (ids : Array Nat) (retain : Bool) (start : Nat)
    (result : RoundResult α) : IO Unit := do
  let finalSize := max baseSize (ids.foldl (fun n i => max n (i + 1)) 0)
  let mut expected := (Array.range finalSize).map (fun i => decide (i < baseSize))
  unless result.history.size == (if retain then ids.size else 0) do
    throw <| IO.userError s!"{label}: wrong snapshot count"
  for i in [0:ids.size] do
    let id := ids[(start + i) % ids.size]!
    if retain then
      let snapshot := result.history[i]!
      unless snapshot.contains (makeKey id) == expected[id]! do
        throw <| IO.userError s!"{label}: snapshot {i} has wrong membership"
      if i > 0 then
        let prev := ids[(start + i - 1) % ids.size]!
        unless snapshot.contains (makeKey prev) do
          throw <| IO.userError s!"{label}: snapshot {i} lost a previous insertion"
    expected := expected.set! id true
  for id in [0:finalSize + 16] do
    let present := if id < finalSize then expected[id]! else false
    unless result.finalSet.contains (makeKey id) == present do
      throw <| IO.userError s!"{label}: incorrect final membership for key {id}"

private def checkPromotion [BEq α] [Hashable α] (map : Lean.PersistentHashSet α)
    (promoted : Bool) : IO Unit := do
  let actual := match map.set.root with
    | .entries es => match es[0]! with
      | .ref (.entries es') => match es'[0]! with
        | .ref (.collision keys _ _) => if keys.size == 3 then some false else none
        | .ref (.entries _) => some true
        | _ => none
      | _ => none
    | _ => none
  unless actual == some promoted do throw <| IO.userError "promotion workload has the wrong shape"

private def runCase [BEq α] [LawfulBEq α] [Hashable α] (label mode : String) (makeKey : Nat → α)
    (baseSize opCount samples targetMs : Nat) : IO Unit := do
  let retain := mode == "snapshots"
  let replacing := mode == "duplicate"
  let mut seed : VerifiedHAMT.Set α := ∅
  for id in [0:baseSize] do
    seed := seed.insert (makeKey id)
  let nativeSeed := seed.toRaw
  let ids := (shuffledIds opCount).map fun i =>
    if replacing then (i * 37) % baseSize else baseSize + i
  let ops := ids.map makeKey
  -- Snapshot workloads insert fresh keys; duplicate workloads reinsert seed
  -- members. Every key occurs once per round, and the rounds rotate their order.
  let expectedDigest := 1 + (if retain then opCount else 0)
  for start in #[0, opCount / 2] do
    let n := nativeRound nativeSeed ops retain start
    let t := totalRound seed ops retain start
    validate (label ++ "/" ++ mode ++ "/native") makeKey baseSize ids retain start n
    validate (label ++ "/" ++ mode ++ "/total") makeKey baseSize ids retain start t
    let last := if start == 0 then opCount - 1 else start - 1
    let probe := makeKey ids[last]!
    unless digest n probe == expectedDigest.toUInt64 &&
        digest t probe == expectedDigest.toUInt64 do
      throw <| IO.userError s!"{label}/{mode}: preview digest mismatch"
    if mode == "promote" then
      checkPromotion nativeSeed false
      checkPromotion n.finalSet true
      checkPromotion t.finalSet true
  let check (rounds : Nat) (n t : Measurement) : IO Unit := do
    let expected := (rounds * expectedDigest).toUInt64
    unless n.checksum == expected && t.checksum == expected do
      throw <| IO.userError s!"{label}/{mode}: timed checksum mismatch"
  let mut rounds := 1
  let mut ready := false
  for _ in [0:20] do
    unless ready do
      let n ← measureNative nativeSeed ops retain rounds
      let t ← measureTotal seed ops retain rounds
      check rounds n t
      if min n.nanos t.nanos >= targetMs * 1000000 then ready := true
      else rounds := rounds * 2
  unless ready do throw <| IO.userError s!"{label}/{mode}: failed to calibrate"
  for sample in [0:samples] do
    let nativeFirst := sample % 2 == 0
    let (n, t) ← if nativeFirst then do
        let n ← measureNative nativeSeed ops retain rounds
        let t ← measureTotal seed ops retain rounds
        pure (n, t)
      else do
        let t ← measureTotal seed ops retain rounds
        let n ← measureNative nativeSeed ops retain rounds
        pure (n, t)
    check rounds n t
    IO.println s!"{label},{mode},{baseSize},{opCount},{rounds},{sample},{nativeFirst},{rounds * opCount},{n.nanos},{t.nanos},{n.checksum}"

private def runNat (label mode : String) (hashFn : Nat → UInt64)
    (baseSize opCount samples targetMs : Nat) : IO Unit := do
  let _ : Hashable Nat := ⟨hashFn⟩
  runCase label mode id baseSize opCount samples targetMs

def run (samples targetMs : Nat) : IO Unit := do
  IO.println "case,mode,base_size,ops_per_round,rounds,sample,native_first,operations,native_ns,total_ns,checksum"
  for count in #[32, 4096, 65536] do
    runNat "nat-default" "build" hash 0 count samples targetMs
  runNat "nat-mixed" "build" (fun n => mixHash 20261001 n.toUInt64) 0 4096 samples targetMs
  runNat "nat-prefix" "build" (fun n => n.toUInt64 <<< 15) 0 4096 samples targetMs
  runNat "nat-collision" "build" (fun _ => 0) 0 128 samples targetMs
  let nameKey := fun n => Lean.Name.num (.str .anonymous "set-bench") n
  runCase "name-default" "build" nameKey 0 16384 samples targetMs
  for size in #[4096, 65536] do
    runNat "nat-default" "duplicate" hash size size samples targetMs
  runNat "nat-prefix" "duplicate" (fun n => n.toUInt64 <<< 15) 4096 4096 samples targetMs
  runNat "nat-collision" "duplicate" (fun _ => 0) 128 128 samples targetMs
  runCase "name-default" "duplicate" nameKey 16384 16384 samples targetMs
  runNat "nat-default" "extend" hash 4096 4096 samples targetMs
  runNat "nat-default" "promote" hash 3072 1024 samples targetMs
  runNat "nat-default" "snapshots" hash 4096 512 samples targetMs
  runNat "nat-prefix" "snapshots" (fun n => n.toUInt64 <<< 15) 4096 512 samples targetMs
  runNat "nat-collision" "snapshots" (fun _ => 0) 128 128 samples targetMs
  runCase "name-default" "snapshots" nameKey 16384 512 samples targetMs

end VerifiedHAMT.SetInsertBenchmarks

def main (args : List String) : IO Unit := do
  let (samples, targetMs) ← match args with
    | [] => pure (9, 20)
    | [s, t] => match s.toNat?, t.toNat? with
      | some s, some t => pure (s, t)
      | _, _ => throw <| IO.userError "usage: setInsertBench [samples target_ms]"
    | _ => throw <| IO.userError "usage: setInsertBench [samples target_ms]"
  unless samples > 0 && targetMs > 0 do throw <| IO.userError "samples and target_ms must be positive"
  VerifiedHAMT.SetInsertBenchmarks.run samples targetMs
