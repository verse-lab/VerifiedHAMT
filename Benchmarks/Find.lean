import VerifiedHAMT

/-! Synthetic, native-code value lookup comparisons. Verified and upstream HAMT
queries share a tree built by the bundled API; Std.HashMap has a separate table.
Construction, validation, warmup, and calibration are outside sample timing. -/

namespace VerifiedHAMT.FindBenchmarks

private structure Measurement where
  nanos : Nat
  checksum : UInt64

@[inline] private def addValue (checksum : UInt64) (value : Option Nat) : UInt64 :=
  match value with
  | none => checksum
  | some v => checksum + v.toUInt64 + 1

-- Direct calls and identical loops; a present zero contributes one to the digest.
@[noinline] private def nativeBatch [BEq α] [Hashable α]
    (map : @& Lean.PersistentHashMap α Nat) (queries : @& Array α)
    (rounds : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:rounds] do
    for key in queries do
      checksum := addValue checksum (map.find? key)
  return checksum

@[noinline] private def verifiedBatch [BEq α] [Hashable α]
    (map : @& Map α Nat) (queries : @& Array α) (rounds : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:rounds] do
    for key in queries do
      checksum := addValue checksum (map.find? key)
  return checksum

@[noinline] private def stdBatch [BEq α] [Hashable α]
    (map : @& Std.HashMap α Nat) (queries : @& Array α) (rounds : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:rounds] do
    for key in queries do
      checksum := addValue checksum (map.get? key)
  return checksum

private def measureNative [BEq α] [Hashable α]
    (map : Lean.PersistentHashMap α Nat) (queries : Array α) (rounds : Nat) : IO Measurement := do
  let start ← IO.monoNanosNow
  let checksum := nativeBatch map queries rounds
  Runtime.hold checksum
  let stop ← IO.monoNanosNow
  return ⟨stop - start, checksum⟩

private def measureVerified [BEq α] [Hashable α]
    (map : Map α Nat) (queries : Array α) (rounds : Nat) : IO Measurement := do
  let start ← IO.monoNanosNow
  let checksum := verifiedBatch map queries rounds
  Runtime.hold checksum
  let stop ← IO.monoNanosNow
  return ⟨stop - start, checksum⟩

private def measureStd [BEq α] [Hashable α]
    (map : Std.HashMap α Nat) (queries : Array α) (rounds : Nat) : IO Measurement := do
  let start ← IO.monoNanosNow
  let checksum := stdBatch map queries rounds
  Runtime.hold checksum
  let stop ← IO.monoNanosNow
  return ⟨stop - start, checksum⟩

private def nextSeed (seed : UInt64) : UInt64 :=
  seed * 6364136223846793005 + 1442695040888963407

private def valueOf (id : Nat) : Nat :=
  if id == 0 then 0 else if id % 3 == 0 then 1000000 + id else id * 17 + 11

private def runCase [BEq α] [LawfulBEq α] [Hashable α]
    (label : String) (makeKey : Nat → α) (size hitPercent samples targetMs : Nat) : IO Unit := do
  let mut map : Map α Nat := ∅
  let mut std : Std.HashMap α Nat := ∅
  for id in [0:size] do
    map := map.insert (makeKey id) (id * 17 + 11)
    std := std.insert (makeKey id) (id * 17 + 11)
  for id in [0:size] do
    if id % 3 == 0 then
      map := map.insert (makeKey id) (valueOf id)
      std := std.insert (makeKey id) (valueOf id)
  let native := map.toRaw
  let queryCount := 8192
  let mut queries := Array.mkEmpty queryCount
  let mut expectedPerRound : UInt64 := 0
  let mut seed : UInt64 := 0x5eed
  for i in [0:queryCount] do
    seed := nextSeed seed
    let id := (seed >>> 32).toNat % (max size 1)
    let isHit := size > 0 && (hitPercent == 100 || (hitPercent == 50 && i % 2 == 0))
    let key := makeKey (if isHit then id else size + id)
    let expected := if isHit then some (valueOf id) else none
    unless native.find? key == expected && map.find? key == expected && std.get? key == expected do
      throw <| IO.userError s!"{label}: synthetic query validation failed"
    expectedPerRound := addValue expectedPerRound expected
    queries := queries.push key
  let check (rounds : Nat) (m : Measurement) : IO Unit := do
    unless m.checksum == expectedPerRound * rounds.toUInt64 do
      throw <| IO.userError s!"{label}: checksum validation failed"
  let mut rounds := 1
  let mut ready := false
  for _ in [0:20] do
    unless ready do
      let n ← measureNative native queries rounds
      let v ← measureVerified map queries rounds
      let s ← measureStd std queries rounds
      check rounds n; check rounds v; check rounds s
      if min n.nanos (min v.nanos s.nanos) >= targetMs * 1000000 then ready := true
      else rounds := rounds * 2
  unless ready do throw <| IO.userError s!"{label}: calibration failed"
  for sample in [0:samples] do
    let mut times := #[0, 0, 0]
    -- Rotate all three backends; each leads equally when samples is divisible by 3.
    for offset in [0:3] do
      let backend := (sample + offset) % 3
      let measurement ← match backend with
        | 0 => measureNative native queries rounds
        | 1 => measureVerified map queries rounds
        | _ => measureStd std queries rounds
      check rounds measurement
      times := times.set! backend measurement.nanos
    IO.println s!"{label},{size},{hitPercent},{sample},{sample % 3},{queryCount * rounds},{times[0]!},{times[1]!},{times[2]!},{expectedPerRound * rounds.toUInt64}"

private def runNat (label : String) (hashFn : Nat → UInt64)
    (size samples targetMs : Nat) : IO Unit := do
  let _ : Hashable Nat := ⟨hashFn⟩
  for hitPercent in #[0, 50, 100] do
    runCase label (fun n : Nat => n) size hitPercent samples targetMs

def run (samples targetMs : Nat) : IO Unit := do
  IO.println "case,size,hit_percent,sample,first,queries,native_ns,verified_ns,std_ns,checksum"
  runCase "nat-empty" (fun n : Nat => n) 0 0 samples targetMs
  runNat "nat-default" hash 32 samples targetMs
  runNat "nat-default" hash 4096 samples targetMs
  runNat "nat-default" hash 65536 samples targetMs
  runNat "nat-identity" Nat.toUInt64 65536 samples targetMs
  runNat "nat-prefix" (fun n => n.toUInt64 <<< 15) 4096 samples targetMs
  runNat "nat-collision" (fun _ => 0) 128 samples targetMs
  for hitPercent in #[0, 50, 100] do
    runCase "name-default" (fun n => Lean.Name.num (.str .anonymous "synthetic") n)
      16384 hitPercent samples targetMs

end VerifiedHAMT.FindBenchmarks

def main (args : List String) : IO Unit := do
  let (samples, targetMs) ← match args with
    | [] => pure (9, 20)
    | [s, t] => match s.toNat?, t.toNat? with
      | some s, some t => pure (s, t)
      | _, _ => throw <| IO.userError "usage: findBench [samples target_ms]"
    | _ => throw <| IO.userError "usage: findBench [samples target_ms]"
  unless samples > 0 && samples % 3 == 0 && targetMs > 0 do
    throw <| IO.userError "samples must be a positive multiple of 3; target_ms must be positive"
  VerifiedHAMT.FindBenchmarks.run samples targetMs
