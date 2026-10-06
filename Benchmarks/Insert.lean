import VerifiedHAMT

/-! Paired native-code insertion measurements. Each round starts from the same
borrowed seed, consumes successive maps, and optionally retains every old map.
Completed rounds are observed and released inside the timed batch. -/

namespace VerifiedHAMT.InsertBenchmarks

private structure RoundResult (α : Type) [BEq α] [Hashable α] where
  finalMap : Lean.PersistentHashMap α Nat
  history : Array (Lean.PersistentHashMap α Nat)

-- Identical loops except for the public insertion function. Salt changes the
-- values each round, preventing loop-invariant reuse of a completed map.
@[noinline] private def nativeRound [BEq α] [Hashable α]
    (seed : @& Lean.PersistentHashMap α Nat) (ops : @& Array (α × Nat))
    (retain : Bool) (salt : Nat) : RoundResult α := Id.run do
  let mut map := seed
  let mut history := #[]
  for (key, value) in ops do
    if retain then history := history.push map
    map := Lean.PersistentHashMap.insert map key (value + salt)
  return ⟨map, history⟩

@[noinline] private def totalRound [BEq α] [Hashable α]
    (seed : @& Lean.PersistentHashMap α Nat) (ops : @& Array (α × Nat))
    (retain : Bool) (salt : Nat) : RoundResult α := Id.run do
  let mut map := seed
  let mut history := #[]
  for (key, value) in ops do
    if retain then history := history.push map
    map := VerifiedHAMT.insert map key (value + salt)
  return ⟨map, history⟩

-- One lookup per completed round, plus one snapshot lookup when retaining
-- history. Keeping this separate also makes the observable result explicit.
@[noinline] private def digest [BEq α] [Hashable α]
    (result : RoundResult α) (probe : α) : UInt64 :=
  let last := (Lean.PersistentHashMap.find? result.finalMap probe).getD 0
  let old := if h : result.history.size > 0 then
      let mid := result.history.size / 2
      (Lean.PersistentHashMap.find? result.history[mid] probe).getD 0
    else 0
  (last + old + result.history.size).toUInt64

@[noinline] private def nativeBatch [BEq α] [Hashable α]
    (seed : @& Lean.PersistentHashMap α Nat) (ops : @& Array (α × Nat))
    (probe : α) (retain : Bool) (rounds : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for round in [0:rounds] do
    checksum := checksum + digest (nativeRound seed ops retain round) probe
  return checksum

@[noinline] private def totalBatch [BEq α] [Hashable α]
    (seed : @& Lean.PersistentHashMap α Nat) (ops : @& Array (α × Nat))
    (probe : α) (retain : Bool) (rounds : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for round in [0:rounds] do
    checksum := checksum + digest (totalRound seed ops retain round) probe
  return checksum

private structure Measurement where
  nanos : Nat
  checksum : UInt64

private def measureNative [BEq α] [Hashable α]
    (seed : Lean.PersistentHashMap α Nat) (ops : Array (α × Nat))
    (probe : α) (retain : Bool) (rounds : Nat) : IO Measurement := do
  let start ← IO.monoNanosNow
  let checksum := nativeBatch seed ops probe retain rounds
  Runtime.hold checksum
  let stop ← IO.monoNanosNow
  return ⟨stop - start, checksum⟩

private def measureTotal [BEq α] [Hashable α]
    (seed : Lean.PersistentHashMap α Nat) (ops : Array (α × Nat))
    (probe : α) (retain : Bool) (rounds : Nat) : IO Measurement := do
  let start ← IO.monoNanosNow
  let checksum := totalBatch seed ops probe retain rounds
  Runtime.hold checksum
  let stop ← IO.monoNanosNow
  return ⟨stop - start, checksum⟩

private def shuffledIds (count : Nat) : Array Nat := Id.run do
  let mut ids := (List.range count).toArray
  let mut state : UInt64 := 0x5eed
  for i in [0:count] do
    state := state * 6364136223846793005 + 1442695040888963407
    let j := i + (state >>> 32).toNat % (count - i)
    ids := ids.swapIfInBounds i j
  return ids

private def validate [BEq α] [Hashable α] (label : String) (makeKey : Nat → α)
    (baseSize : Nat) (ids : Array Nat) (ops : Array (α × Nat)) (retain : Bool)
    (salt : Nat) (result : RoundResult α) : IO Unit := do
  let finalSize := max baseSize (ids.foldl (fun n i => max n (i + 1)) 0)
  let mut expected : Array (Option Nat) := (Array.range finalSize).map fun i =>
    if i < baseSize then some i else none
  unless result.history.size == (if retain then ops.size else 0) do
    throw <| IO.userError s!"{label}: wrong snapshot count"
  for h : i in [0:ops.size] do
    let id := ids[i]!
    if retain then
      -- At each retained snapshot check the just-about-to-be-written key and,
      -- when present, the preceding operation's key/value.
      let snapshot := result.history[i]!
      unless snapshot.find? (makeKey id) == expected[id]! do
        throw <| IO.userError s!"{label}: snapshot {i} lost its old value"
      if i > 0 then
        let prev := ids[i - 1]!
        unless snapshot.find? (makeKey prev) == expected[prev]! do
          throw <| IO.userError s!"{label}: snapshot {i} lost a previous insertion"
    expected := expected.set! id (some (ops[i].2 + salt))
  for id in [0:finalSize + 16] do
    let value := if id < finalSize then expected[id]! else none
    unless result.finalMap.find? (makeKey id) == value do
      throw <| IO.userError s!"{label}: incorrect final value for key {id}"

private def checkPromotion [BEq α] [Hashable α] (map : Lean.PersistentHashMap α Nat)
    (promoted : Bool) : IO Unit := do
  let actual := match map.root with
    | .entries es => match es[0]! with
      | .ref (.entries es') => match es'[0]! with
        | .ref (.collision keys _ _) => if keys.size == 3 then some false else none
        | .ref (.entries _) => some true
        | _ => none
      | _ => none
    | _ => none
  unless actual == some promoted do throw <| IO.userError "promotion workload has the wrong shape"

private def runCase [BEq α] [Hashable α] (label mode : String) (makeKey : Nat → α)
    (baseSize opCount samples targetMs : Nat) : IO Unit := do
  let retain := mode == "snapshots"
  let replacing := mode == "replace" || retain
  let mut seed : Lean.PersistentHashMap α Nat := {}
  for id in [0:baseSize] do
    seed := Lean.PersistentHashMap.insert seed (makeKey id) id
  let ids := (shuffledIds opCount).map fun i =>
    if replacing then (i * 37) % baseSize else baseSize + i
  let ops := ids.map fun id => (makeKey id, 1000000 + id)
  let probeId := ids.back!
  let probe := makeKey probeId
  -- Every operation in a round uses a distinct key. The last operation's key
  -- has its seed value in every old snapshot, so the digest is known independently.
  let expectedDigest := 1000000 + probeId + (if retain then probeId + opCount else 0)
  for salt in #[0, 3] do
    let n := nativeRound seed ops retain salt
    let t := totalRound seed ops retain salt
    validate (label ++ "/" ++ mode ++ "/native") makeKey baseSize ids ops retain salt n
    validate (label ++ "/" ++ mode ++ "/total") makeKey baseSize ids ops retain salt t
    unless digest n probe == (expectedDigest + salt).toUInt64 &&
        digest t probe == (expectedDigest + salt).toUInt64 do
      throw <| IO.userError s!"{label}/{mode}: preview digest mismatch"
    if mode == "promote" then
      checkPromotion seed false
      checkPromotion n.finalMap true
      checkPromotion t.finalMap true
  let check (rounds : Nat) (n t : Measurement) : IO Unit := do
    let expected := (rounds * expectedDigest + rounds * (rounds - 1) / 2).toUInt64
    unless n.checksum == expected && t.checksum == expected do
      throw <| IO.userError s!"{label}/{mode}: timed checksum mismatch"
  let mut rounds := 1
  let mut ready := false
  for _ in [0:20] do
    unless ready do
      let n ← measureNative seed ops probe retain rounds
      let t ← measureTotal seed ops probe retain rounds
      check rounds n t
      if min n.nanos t.nanos >= targetMs * 1000000 then ready := true
      else rounds := rounds * 2
  unless ready do throw <| IO.userError s!"{label}/{mode}: failed to calibrate"
  for sample in [0:samples] do
    let nativeFirst := sample % 2 == 0
    let (n, t) ← if nativeFirst then do
        let n ← measureNative seed ops probe retain rounds
        let t ← measureTotal seed ops probe retain rounds
        pure (n, t)
      else do
        let t ← measureTotal seed ops probe retain rounds
        let n ← measureNative seed ops probe retain rounds
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
  runNat "nat-mixed" "build" (fun n => mixHash 0x5eed n.toUInt64) 0 4096 samples targetMs
  runNat "nat-prefix" "build" (fun n => n.toUInt64 <<< 15) 0 4096 samples targetMs
  runNat "nat-collision" "build" (fun _ => 0) 0 128 samples targetMs
  let nameKey := fun n => Lean.Name.num (.str .anonymous "insert-bench") n
  runCase "name-default" "build" nameKey 0 16384 samples targetMs
  for size in #[4096, 65536] do
    runNat "nat-default" "replace" hash size size samples targetMs
  runNat "nat-prefix" "replace" (fun n => n.toUInt64 <<< 15) 4096 4096 samples targetMs
  runNat "nat-collision" "replace" (fun _ => 0) 128 128 samples targetMs
  runCase "name-default" "replace" nameKey 16384 16384 samples targetMs
  runNat "nat-default" "extend" hash 4096 4096 samples targetMs
  runNat "nat-default" "promote" hash 3072 1024 samples targetMs
  runNat "nat-default" "snapshots" hash 4096 512 samples targetMs
  runNat "nat-prefix" "snapshots" (fun n => n.toUInt64 <<< 15) 4096 512 samples targetMs
  runNat "nat-collision" "snapshots" (fun _ => 0) 128 128 samples targetMs
  runCase "name-default" "snapshots" nameKey 16384 512 samples targetMs

end VerifiedHAMT.InsertBenchmarks

def main (args : List String) : IO Unit := do
  let (samples, targetMs) ← match args with
    | [] => pure (9, 20)
    | [s, t] => match s.toNat?, t.toNat? with
      | some s, some t => pure (s, t)
      | _, _ => throw <| IO.userError "usage: insertBench [samples target_ms]"
    | _ => throw <| IO.userError "usage: insertBench [samples target_ms]"
  unless samples > 0 && targetMs > 0 do throw <| IO.userError "samples and target_ms must be positive"
  VerifiedHAMT.InsertBenchmarks.run samples targetMs
