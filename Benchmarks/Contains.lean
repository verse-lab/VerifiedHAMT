import HAMTVerify

/-!
Native-code benchmark of the public total and upstream partial `contains` APIs.
Map construction, query generation, validation, warmup, and calibration are not
timed. Paired samples alternate execution order and check both checksums.
-/

namespace HAMTVerify.Benchmarks

private structure Measurement where
  nanos : Nat
  checksum : UInt64

-- Keep the two hot loops identical apart from the lookup implementation. Direct
-- calls avoid a per-query function-pointer dispatch in the benchmark harness.
@[noinline] private def nativeBatch [BEq α] [Hashable α]
    (map : @& Lean.PersistentHashMap α Nat) (queries : @& Array α)
    (rounds : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:rounds] do
    for key in queries do
      if map.contains key then checksum := checksum + 1
  return checksum

@[noinline] private def totalBatch [BEq α] [Hashable α]
    (map : @& Lean.PersistentHashMap α Nat) (queries : @& Array α)
    (rounds : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:rounds] do
    for key in queries do
      if HAMTVerify.contains map key then checksum := checksum + 1
  return checksum

private def measureNative [BEq α] [Hashable α]
    (map : Lean.PersistentHashMap α Nat) (queries : Array α)
    (rounds : Nat) : IO Measurement := do
  let start ← IO.monoNanosNow
  let checksum := nativeBatch map queries rounds
  -- This observable dependency prevents Lean from sinking the pure batch past
  -- the second clock read. A plain `let checksum := ...` is not sufficient.
  Runtime.hold checksum
  let stop ← IO.monoNanosNow
  return ⟨stop - start, checksum⟩

private def measureTotal [BEq α] [Hashable α]
    (map : Lean.PersistentHashMap α Nat) (queries : Array α)
    (rounds : Nat) : IO Measurement := do
  let start ← IO.monoNanosNow
  let checksum := totalBatch map queries rounds
  Runtime.hold checksum
  let stop ← IO.monoNanosNow
  return ⟨stop - start, checksum⟩

private def nextSeed (seed : UInt64) : UInt64 :=
  seed * 6364136223846793005 + 1442695040888963407

private def runCase [BEq α] [Hashable α] (label : String) (makeKey : Nat → α)
    (size hitPercent samples targetMs : Nat) : IO Unit := do
  let mut map : Lean.PersistentHashMap α Nat := {}
  for i in [0:size] do
    map := map.insert (makeKey i) i
  let queryCount := 8192
  let mut queries := Array.mkEmpty queryCount
  let mut expectedHits : UInt64 := 0
  let mut seed : UInt64 := 20261001
  for i in [0:queryCount] do
    seed := nextSeed seed
    let id := (seed >>> 32).toNat % (max size 1)
    let isHit := size > 0 && (hitPercent == 100 || (hitPercent == 50 && i % 2 == 0))
    let key := makeKey (if isHit then id else size + id)
    -- Independent expected membership follows from inserted IDs, not one of
    -- the implementations being measured. Check every query before timing.
    unless map.contains key == isHit && HAMTVerify.contains map key == isHit do
      throw <| IO.userError s!"{label}: incorrect result for query {i}"
    if isHit then expectedHits := expectedHits + 1
    queries := queries.push key
  -- Warm both implementations before choosing a common batch size. Use the
  -- faster time to ensure that *both* measured batches reach the target time.
  let mut rounds := 1
  let mut ready := false
  for _ in [0:20] do
    unless ready do
      let n ← measureNative map queries rounds
      let t ← measureTotal map queries rounds
      let expected := expectedHits * rounds.toUInt64
      unless n.checksum == expected && t.checksum == expected do
        throw <| IO.userError s!"{label}: calibration checksum mismatch"
      if min n.nanos t.nanos >= targetMs * 1000000 then
        ready := true
      else
        rounds := rounds * 2
  unless ready do
    throw <| IO.userError s!"{label}: failed to calibrate"
  for sample in [0:samples] do
    let nativeFirst := sample % 2 == 0
    let (n, t) ← if nativeFirst then do
        let n ← measureNative map queries rounds
        let t ← measureTotal map queries rounds
        pure (n, t)
      else do
        let t ← measureTotal map queries rounds
        let n ← measureNative map queries rounds
        pure (n, t)
    let expected := expectedHits * rounds.toUInt64
    unless n.checksum == expected && t.checksum == expected do
      throw <| IO.userError s!"{label}: timed checksum mismatch"
    IO.println s!"{label},{size},{hitPercent},{sample},{nativeFirst},{queryCount * rounds},{n.nanos},{t.nanos},{expected}"

private def runNat (label : String) (hashFn : Nat → UInt64) (size samples targetMs : Nat) : IO Unit := do
  let _ : Hashable Nat := ⟨hashFn⟩
  for hitPercent in #[0, 50, 100] do
    runCase label (fun n : Nat => n) size hitPercent samples targetMs

def run (samples targetMs : Nat) : IO Unit := do
  IO.println "case,size,hit_percent,sample,native_first,queries,native_ns,total_ns,checksum"
  runCase "nat-empty" (fun n : Nat => n) 0 0 samples targetMs
  runNat "nat-default" hash 32 samples targetMs
  runNat "nat-default" hash 4096 samples targetMs
  runNat "nat-default" hash 65536 samples targetMs
  runNat "nat-identity" Nat.toUInt64 65536 samples targetMs
  runNat "nat-prefix" (fun n => n.toUInt64 <<< 15) 4096 samples targetMs
  runNat "nat-collision" (fun _ => 0) 128 samples targetMs
  for hitPercent in #[0, 50, 100] do
    runCase "name-default" (fun n => Lean.Name.num (.str .anonymous "bench") n)
      16384 hitPercent samples targetMs

end HAMTVerify.Benchmarks

def main (args : List String) : IO Unit := do
  let (samples, targetMs) ← match args with
    | [] => pure (9, 20)
    | [s, t] => match s.toNat?, t.toNat? with
      | some s, some t => pure (s, t)
      | _, _ => throw <| IO.userError "usage: containsBench [samples target_ms]"
    | _ => throw <| IO.userError "usage: containsBench [samples target_ms]"
  unless samples > 0 && targetMs > 0 do
    throw <| IO.userError "samples and target_ms must be positive"
  HAMTVerify.Benchmarks.run samples targetMs
