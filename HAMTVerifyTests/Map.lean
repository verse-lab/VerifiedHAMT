import HAMTVerify.Map

/-! Client-side examples: no separate routing or uniqueness hypotheses. -/

namespace HAMTVerify.MapTests

open HAMTVerify.Map

example [BEq α] [LawfulBEq α] [Hashable α] (map : Map α β) (key : α) :
    map.contains key = true ↔ key ∈ map := Map.contains_eq_true_iff map key

example [BEq α] [LawfulBEq α] [Hashable α] (map : Map α β) (key q : α) (value : β) :
    (map.insert key value).contains q = ((q == key) || map.contains q) := by simp

-- Insertion and its theorems require no Inhabited or BEq instance on values.
example [BEq α] [LawfulBEq α] [Hashable α] (map : Map α β) (key : α) (v w : β) :
    (map.insert key v).MapsTo key w ↔ w = v := by simp

example [BEq α] [LawfulBEq α] [Hashable α] (map : Map α β)
    (key q : α) (v w : β) (hne : q ≠ key) :
    (map.insert key v).MapsTo q w ↔ map.MapsTo q w := by simp [hne]

example [BEq α] [LawfulBEq α] [Hashable α] (map : Map α β) (key : α) (v₁ v₂ w : β) :
    ((map.insert key v₁).insert key v₂).MapsTo key w ↔ w = v₂ := by simp

-- Invariants are available when explicitly exporting to the lower-level API.
example [BEq α] [LawfulBEq α] [Hashable α] (xs : List (α × β)) :
    Valid (Map.ofList xs).toRaw ∧ Unique (Map.ofList xs).toRaw.root :=
  ⟨(Map.ofList xs).valid, (Map.ofList xs).unique⟩

example (raw : Lean.PersistentHashMap Nat Nat) (hv : Valid raw) (hu : Unique raw.root) :
    (Map.ofRaw raw hv hu).toRaw = raw := by simp

example : (Map.ofList [(1, 10), (2, 20), (1, 99)]).MapsTo 1 99 := by
  simp [Map.ofList]

example : (Map.ofList [(1, 10), (2, 20), (1, 99)]).MapsTo 2 20 := by
  simp [Map.ofList]

-- The size counts keys: overwriting keeps it, a new key adds one.
example [BEq α] [LawfulBEq α] [Hashable α] (map : Map α β) (key : α) (v w : β) :
    ((map.insert key v).insert key w).size = (map.insert key v).size := by
  simp [Map.size_insert]

example [BEq α] [Hashable α] (map : Map α β) :
    ∃ keys : List α, keys.Nodup ∧ (∀ k, k ∈ keys ↔ k ∈ map) ∧ keys.length = map.size :=
  ⟨map.keys, map.nodup_keys, map.mem_keys, map.length_keys⟩

-- Standard collection notation and the executable structural membership instance.
#guard ({(1, 10), (2, 20)} : Map Nat Nat).contains 2
#guard decide (2 ∈ (Map.ofList [(1, 10), (2, 20)]))
#guard !decide (3 ∈ (Map.ofList [(1, 10), (2, 20)]))
#guard (Map.ofList [(1, 10), (2, 20), (1, 99)]).size == 2
#guard (∅ : Map Nat Nat).size == 0

/-- info: 'HAMTVerify.Map.contains_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Map.contains_eq_true_iff
/-- info: 'HAMTVerify.Map.mapsTo_insert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Map.mapsTo_insert_iff
/-- info: 'HAMTVerify.Map.size_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Map.size_insert
/-- info: 'HAMTVerify.Map.length_keys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Map.length_keys

/-- The runtime data of `Map`: the native map and its size, without the proofs. -/
abbrev SizedRaw := HAMTVerify.SizedRaw

-- Compile paired entry points to inspect erasure of the wrapper and proof fields.
@[noinline] def wrappedInsert (map : Map Nat Nat) (key value : Nat) : Map Nat Nat :=
  map.insert key value

@[noinline] def rawInsert (map : SizedRaw Nat Nat) (key value : Nat) : SizedRaw Nat Nat :=
  HAMTVerify.insertSizedImpl map key value

@[noinline] def wrappedContains (map : Map Nat Nat) (key : Nat) : Bool :=
  map.contains key

@[noinline] def rawContains (map : SizedRaw Nat Nat) (key : Nat) : Bool :=
  HAMTVerify.contains map.toRaw key

/-- Exercise bulk construction, collision promotion, snapshots, and the public
membership decision through the bundled API. Native value lookup is only a test oracle. -/
def run : IO Unit := do
  let _ : Hashable Nat := ⟨fun _ => 0⟩
  let bindings := (List.range 32).map fun key => (key, key + 100)
  let original := Map.ofList bindings
  let changed := original.insert 7 999 |>.insert 32 132
  for key in [0:34] do
    unless original.contains key == (key < 32) && changed.contains key == (key < 33) do
      throw <| IO.userError "bundled map membership mismatch"
    unless decide (key ∈ changed) == changed.contains key do
      throw <| IO.userError "bundled map membership decision mismatch"
  unless original.toRaw.find? 7 == some 107 && changed.toRaw.find? 7 == some 999 &&
      changed.toRaw.find? 32 == some 132 do
    throw <| IO.userError "bundled map overwrite or snapshot mismatch"
  let imported := Map.ofRaw changed.toRaw changed.valid changed.unique
  unless original.size == 32 && changed.size == 33 && imported.size == 33 &&
      changed.keys.length == 33 && (Map.ofList (bindings ++ bindings)).size == 32 do
    throw <| IO.userError "bundled map size mismatch"
  IO.println "map: bundled API, bulk construction, collisions, overwrites, sizes, and snapshots passed."

end HAMTVerify.MapTests
