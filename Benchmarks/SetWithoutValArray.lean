import VerifiedHAMT

/-! Five-way native-code comparison. `raw` uses the existing total insertion on
`PersistentHashMap α Unit` without a cached size, providing a representation-only
control. `bundled` is the existing public Set API (with cached size), `bare` is
the unsized keys-only raw set, and `keys` is its verified public API with a count.
Higher-order round/batch functions specialize to direct calls for each backend. -/

namespace VerifiedHAMT.KeysOnlyBench

private structure Result (σ : Type) where
  finalSet : σ
  history : Array σ

@[noinline, specialize] private def round (insert : σ → α → σ)
    (seed : @& σ) (ops : @& Array α) (retain : Bool) (start : Nat) : Result σ := Id.run do
  let mut set := seed
  let mut history := #[]
  for h : i in [start:ops.size] do
    if retain then history := history.push set
    set := insert set ops[i]
  for i in [0:start] do
    if h : i < ops.size then
      if retain then history := history.push set
      set := insert set ops[i]
  return ⟨set, history⟩

@[noinline, specialize] private def digest (contains : σ → α → Bool)
    (result : Result σ) (probe : α) : UInt64 :=
  let last := if contains result.finalSet probe then 1 else 0
  let old := if h : result.history.size > 0 then
      if contains result.history[result.history.size / 2] probe then 1 else 0
    else 0
  (last + old + result.history.size).toUInt64

@[noinline, specialize] private def insertBatch
    (insert : σ → α → σ) (contains : σ → α → Bool)
    (seed : @& σ) (ops : @& Array α) (retain : Bool) (rounds : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for r in [0:rounds] do
    let start := r % ops.size
    let last := if start == 0 then ops.size - 1 else start - 1
    if h : last < ops.size then
      checksum := checksum + digest contains (round insert seed ops retain start) ops[last]
  return checksum

@[noinline, specialize] private def containsBatch (contains : σ → α → Bool)
    (set : @& σ) (queries : @& Array α) (rounds : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:rounds] do
    for key in queries do
      if contains set key then checksum := checksum + 1
  return checksum

private structure Measurement where
  nanos : Nat
  checksum : UInt64

private def measure (batch : Nat → UInt64) (rounds : Nat) : IO Measurement := do
  let start ← IO.monoNanosNow
  let checksum := batch rounds
  Runtime.hold checksum
  let stop ← IO.monoNanosNow
  return ⟨stop - start, checksum⟩

-- A batch closure is invoked once per clock interval, never per operation.
private def sample (label mode : String) (size opCount expected samples targetMs : Nat)
    (batches : Array (Nat → UInt64)) : IO Unit := do
  let checked (i rounds : Nat) : IO Measurement := do
    let m ← measure batches[i]! rounds
    unless m.checksum == (expected * rounds).toUInt64 do
      throw <| IO.userError s!"{label}/{mode}/{i}: checksum mismatch"
    return m
  let mut rounds := 1
  let mut ready := false
  for _ in [0:24] do
    unless ready do
      let mut shortest := targetMs * 1000000
      for i in [0:batches.size] do
        shortest := min shortest (← checked i rounds).nanos
      if shortest >= targetMs * 1000000 then ready := true
      else rounds := rounds * 2
  unless ready do throw <| IO.userError s!"{label}/{mode}: failed to calibrate"
  for s in [0:samples] do
    let mut times := Array.replicate batches.size 0
    -- Rotate execution order so each backend runs first.
    for j in [0:batches.size] do
      let i := (s + j) % batches.size
      times := times.set! i (← checked i rounds).nanos
    IO.println s!"{label},{mode},{size},{opCount},{s},{s % batches.size},{rounds},{times[0]!},{times[1]!},{times[2]!},{times[3]!},{times[4]!},{expected * rounds}"

private def shuffled (count : Nat) : Array Nat := Id.run do
  let mut ids := Array.range count
  let mut state : UInt64 := 0xc0ffee
  for i in [0:count] do
    state := state * 6364136223846793005 + 1442695040888963407
    ids := ids.swapIfInBounds i (i + (state >>> 32).toNat % (count - i))
  return ids

private def validate [Inhabited σ] (contains : σ → α → Bool) (keyOf : Nat → α)
    (baseSize : Nat) (ids : Array Nat) (retain : Bool) (start : Nat)
    (result : Result σ) : IO Unit := do
  let finalSize := max baseSize (ids.foldl (fun n i => max n (i + 1)) 0)
  let mut expected := (Array.range finalSize).map (fun i => decide (i < baseSize))
  unless result.history.size == (if retain then ids.size else 0) do
    throw <| IO.userError "wrong snapshot count"
  for i in [0:ids.size] do
    let id := ids[(start + i) % ids.size]!
    if retain then
      let old := result.history[i]!
      unless contains old (keyOf id) == expected[id]! do
        throw <| IO.userError "snapshot contains future insertion"
      if i > 0 then
        unless contains old (keyOf ids[(start + i - 1) % ids.size]!) do
          throw <| IO.userError "snapshot lost previous insertion"
    expected := expected.set! id true
  for id in [0:finalSize + 16] do
    unless contains result.finalSet (keyOf id) ==
        (if id < finalSize then expected[id]! else false) do
      throw <| IO.userError "final membership mismatch"

private def runCase [BEq α] [LawfulBEq α] [Hashable α]
    (label mode : String) (keyOf : Nat → α)
    (size opCount samples targetMs : Nat) : IO Unit := do
  let mut bundled : VerifiedHAMT.Set α := ∅
  let mut keys : SetWithoutValArray α := ∅
  for i in [0:size] do
    bundled := bundled.insert (keyOf i)
    keys := keys.insert (keyOf i)
  let native := bundled.toRaw
  let raw := bundled.toMap.toRaw
  let bare := keys.toRaw
  if mode.startsWith "contains" then
    let hits := (mode.drop 9).toString.toNat!.min 100
    let mut queries := Array.mkEmpty opCount
    let mut expected := 0
    let mut state : UInt64 := 0xc0ffee
    for i in [0:opCount] do
      state := state * 6364136223846793005 + 1442695040888963407
      let id := (state >>> 32).toNat % max size 1
      let found := size > 0 && (hits == 100 || (hits == 50 && i % 2 == 0))
      let q := keyOf (if found then id else size + id)
      unless native.contains q == found && VerifiedHAMT.contains raw q == found &&
          bundled.contains q == found && bare.contains q == found && keys.contains q == found do
        throw <| IO.userError s!"{label}/{mode}: lookup mismatch"
      queries := queries.push q
      if found then expected := expected + 1
    sample label mode size opCount expected samples targetMs #[
      containsBatch Lean.PersistentHashSet.contains native queries,
      containsBatch VerifiedHAMT.contains raw queries,
      containsBatch VerifiedHAMT.Set.contains bundled queries,
      containsBatch SetWithoutValArray.Raw.contains bare queries,
      containsBatch SetWithoutValArray.contains keys queries]
  else
    let retain := mode == "snapshots"
    let ids := (shuffled opCount).map fun i => if mode == "duplicate" then i % size else size + i
    let ops := ids.map keyOf
    let rawInsert := fun s k => VerifiedHAMT.insert s k ()
    for start in #[0, opCount / 2] do
      validate Lean.PersistentHashSet.contains keyOf size ids retain start
        (round Lean.PersistentHashSet.insert native ops retain start)
      validate VerifiedHAMT.contains keyOf size ids retain start (round rawInsert raw ops retain start)
      validate VerifiedHAMT.Set.contains keyOf size ids retain start
        (round VerifiedHAMT.Set.insert bundled ops retain start)
      validate SetWithoutValArray.contains keyOf size ids retain start
        (round SetWithoutValArray.insert keys ops retain start)
      validate SetWithoutValArray.Raw.contains keyOf size ids retain start
        (round SetWithoutValArray.Raw.insert bare ops retain start)
    sample label mode size opCount (1 + if retain then opCount else 0) samples targetMs #[
      insertBatch Lean.PersistentHashSet.insert Lean.PersistentHashSet.contains native ops retain,
      insertBatch rawInsert VerifiedHAMT.contains raw ops retain,
      insertBatch VerifiedHAMT.Set.insert VerifiedHAMT.Set.contains bundled ops retain,
      insertBatch SetWithoutValArray.Raw.insert SetWithoutValArray.Raw.contains bare ops retain,
      insertBatch SetWithoutValArray.insert SetWithoutValArray.contains keys ops retain]

private def runNat (label mode : String) (hashFn : Nat → UInt64)
    (size opCount samples targetMs : Nat) : IO Unit := do
  let _ : Hashable Nat := ⟨hashFn⟩
  runCase label mode id size opCount samples targetMs

def run (samples targetMs : Nat) : IO Unit := do
  IO.println "case,mode,size,ops,sample,first,rounds,native_ns,raw_ns,bundled_ns,bare_ns,keys_ns,checksum"
  for count in #[32, 4096, 65536] do
    runNat "nat-default" "build" hash 0 count samples targetMs
  runNat "nat-mixed" "build" (fun n => mixHash 0xc0ffee n.toUInt64) 0 4096 samples targetMs
  runNat "nat-prefix" "build" (fun n => n.toUInt64 <<< 15) 0 4096 samples targetMs
  runNat "nat-collision" "build" (fun _ => 0) 0 128 samples targetMs
  let nameKey := fun n => Lean.Name.num `keysOnlyBench n
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
  runNat "nat-empty" "contains-0" hash 0 8192 samples targetMs
  for hits in #[0, 50, 100] do
    let mode := s!"contains-{hits}"
    for size in #[32, 4096, 65536] do
      runNat "nat-default" mode hash size 8192 samples targetMs
    runNat "nat-identity" mode Nat.toUInt64 65536 8192 samples targetMs
    runNat "nat-prefix" mode (fun n => n.toUInt64 <<< 15) 4096 8192 samples targetMs
    runNat "nat-collision" mode (fun _ => 0) 128 8192 samples targetMs
    runCase "name-default" mode nameKey 16384 8192 samples targetMs

end VerifiedHAMT.KeysOnlyBench

def main (args : List String) : IO Unit := do
  let (samples, targetMs) ← match args with
    | [] => pure (10, 20)
    | [s, t] => match s.toNat?, t.toNat? with
      | some s, some t => pure (s, t)
      | _, _ => throw <| IO.userError "usage: setWithoutValArrayBench [samples target_ms]"
    | _ => throw <| IO.userError "usage: setWithoutValArrayBench [samples target_ms]"
  unless samples > 0 && targetMs > 0 do throw <| IO.userError "arguments must be positive"
  VerifiedHAMT.KeysOnlyBench.run samples targetMs
