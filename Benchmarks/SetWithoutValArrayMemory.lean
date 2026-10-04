import HAMTVerify

/-! Runtime storage accounting, outside all timed regions. This deliberately
unsafe diagnostic uses the pinned Lean runtime ABI, never a proof or library API.
Count each reachable node, entry, and array once by address, including array
capacity, and the cached-size carriers. Exclude key payloads, outer history
arrays, and allocator metadata/pages. This is not process RSS. -/

namespace HAMTVerify.KeysOnlyMemory

@[extern "lean_object_byte_size"]
private unsafe opaque objectBytes {α : Type} (obj : @& α) : USize

private structure Footprint where
  seen : Std.HashSet USize := {}
  bytes : Nat := 0
  objects : Nat := 0

private unsafe def record (obj : @& α) (acc : Footprint) : Bool × Footprint :=
  if isScalarObj obj then (false, acc)
  else
    let addr := ptrAddrUnsafe obj
    if acc.seen.contains addr then (false, acc)
    else (true, {
      seen := acc.seen.insert addr
      bytes := acc.bytes + (objectBytes obj).toNat
      objects := acc.objects + 1 })

private unsafe def recordArray (a : @& Array α) (acc : Footprint) : Footprint :=
  (record a acc).2

private unsafe def nativeNode (node : @& Lean.PersistentHashMap.Node α Unit)
    (acc : Footprint) : Footprint := Id.run do
  let (fresh, acc) := record node acc
  unless fresh do return acc
  match node with
  | .collision keys vals _ => return recordArray vals (recordArray keys acc)
  | .entries es =>
    let (fresh, acc) := record es acc
    unless fresh do return acc
    return es.foldl (fun acc e =>
      let (fresh, acc) := record e acc
      if !fresh then acc else match e with
        | .ref child => nativeNode child acc
        | _ => acc) acc

private unsafe def keysNode (node : @& SetWithoutValArray.Node α)
    (acc : Footprint) : Footprint := Id.run do
  let (fresh, acc) := record node acc
  unless fresh do return acc
  match node with
  | .collision keys => return recordArray keys acc
  | .entries es =>
    let (fresh, acc) := record es acc
    unless fresh do return acc
    return es.foldl (fun acc e =>
      let (fresh, acc) := record e acc
      if !fresh then acc else match e with
        | .ref child => keysNode child acc
        | _ => acc) acc

private unsafe def runCase [BEq α] [LawfulBEq α] [Hashable α]
    (label : String) (keyOf : Nat → α) (size snapshots : Nat) : IO Unit := do
  let mut native : Lean.PersistentHashSet α := ∅
  let mut raw : Lean.PersistentHashMap α Unit := {}
  let mut bundled : Set α := ∅
  let mut keys : SetWithoutValArray α := ∅
  for i in [0:size] do
    let key := keyOf i
    native := native.insert key
    raw := HAMTVerify.insert raw key ()
    bundled := bundled.insert key
    keys := keys.insert key
  let mut ns := #[]
  let mut rs := #[]
  let mut ks := #[]
  let mut bs := #[]
  for i in [0:snapshots] do
    ns := ns.push native
    rs := rs.push raw
    ks := ks.push keys
    bs := bs.push bundled
    let key := keyOf (size + i)
    native := native.insert key
    raw := HAMTVerify.insert raw key ()
    bundled := bundled.insert key
    keys := keys.insert key
  ns := ns.push native
  rs := rs.push raw
  ks := ks.push keys
  bs := bs.push bundled
  let n := ns.foldl (fun acc s => nativeNode s.set.root acc) {}
  let r := rs.foldl (fun acc s => nativeNode s.root acc) {}
  let bare := ks.foldl (fun acc s => keysNode s.toRaw.root acc) {}
  let k := ks.foldl (fun acc s => (record s.toSizedRaw acc).2) bare
  let b := bs.foldl (fun acc s => nativeNode s.toRaw.set.root ((record s.toMap.toSizedRaw acc).2)) {}
  -- Roots remain live throughout address-based traversal, so the allocator
  -- cannot reuse their addresses while the diagnostic still remembers them.
  Runtime.hold (ns, rs, ks, bs)
  unless keys.size == size + snapshots && n.bytes > 0 && k.bytes > 0 do
    throw <| IO.userError "memory workload validation failed"
  IO.println s!"{label},{size},{snapshots},{n.bytes},{r.bytes},{b.bytes},{bare.bytes},{k.bytes},{n.objects},{r.objects},{b.objects},{bare.objects},{k.objects}"

private unsafe def runNat (label : String) (hashFn : Nat → UInt64)
    (size snapshots : Nat) : IO Unit := do
  let _ : Hashable Nat := ⟨hashFn⟩
  runCase label id size snapshots

unsafe def run : IO Unit := do
  -- Sharing must be counted once; this also exercises the runtime FFI.
  let a := Array.replicate 100 (0 : Nat)
  let once := recordArray a {}
  let twice := recordArray a once
  unless once.bytes > 100 * (System.Platform.numBits / 8) &&
      once.bytes == twice.bytes && twice.objects == 1 do
    throw <| IO.userError "unexpected runtime array accounting"
  Runtime.hold a
  IO.println "case,size,snapshots,native_bytes,raw_bytes,bundled_bytes,bare_bytes,keys_bytes,native_objects,raw_objects,bundled_objects,bare_objects,keys_objects"
  for size in #[32, 4096, 65536, 1048576] do
    runNat "nat-default" hash size 0
  runNat "nat-prefix" (fun n => n.toUInt64 <<< 15) 4096 0
  runNat "nat-collision" (fun _ => 0) 4096 0
  runCase "name-default" (fun n => Lean.Name.num `keysOnlyBench n) 16384 0
  runNat "nat-default" hash 4096 512
  runNat "nat-prefix" (fun n => n.toUInt64 <<< 15) 4096 512
  runNat "nat-collision" (fun _ => 0) 128 128

end HAMTVerify.KeysOnlyMemory

unsafe def main : IO Unit := HAMTVerify.KeysOnlyMemory.run
