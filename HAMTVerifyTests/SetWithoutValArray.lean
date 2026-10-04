import HAMTVerify

namespace HAMTVerify.SetWithoutValArrayTests

open scoped HAMTVerify.SetWithoutValArray

example [BEq α] [Hashable α] [LawfulBEq α] (xs : List α) (key : α) :
    key ∈ SetWithoutValArray.ofList xs ↔ key ∈ xs := by simp

example [BEq α] [Hashable α] [LawfulBEq α] (s : SetWithoutValArray α) (key q : α) :
    (s.insert key).contains q = ((q == key) || s.contains q) := by simp

example [BEq α] [Hashable α] [LawfulBEq α] (s : SetWithoutValArray α) (key : α) :
    ((s.insert key).insert key).size = (s.insert key).size := by
  simp [SetWithoutValArray.size_insert]

example [BEq α] [Hashable α] (s : SetWithoutValArray α) :
    ∃ keys : List α, keys.Nodup ∧ (∀ k, k ∈ keys ↔ k ∈ s) ∧ keys.length = s.size :=
  ⟨s.toList, s.nodup_toList, s.mem_toList, s.length_toList⟩

example [BEq α] [Hashable α] (s : SetWithoutValArray α) :
    SetWithoutValArray.ofRaw s.toRaw s.valid s.unique = s := by simp

#guard ({1, 2, 1} : SetWithoutValArray Nat).size == 2
#guard decide (2 ∈ ({1, 2, 1} : SetWithoutValArray Nat))
#guard !decide (3 ∈ ({1, 2, 1} : SetWithoutValArray Nat))
#guard (SetWithoutValArray.ofList [7, 3, 7]).contains 3
#guard SetWithoutValArray.Raw.containsNode (.entries #[]) 0 7 == false

/-- info: 'HAMTVerify.SetWithoutValArray.contains_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SetWithoutValArray.contains_eq_true_iff
/-- info: 'HAMTVerify.SetWithoutValArray.mem_insert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SetWithoutValArray.mem_insert_iff
/-- info: 'HAMTVerify.SetWithoutValArray.size_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SetWithoutValArray.size_insert
/-- info: 'HAMTVerify.SetWithoutValArray.Raw.insertSized_eq_impl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SetWithoutValArray.Raw.insertSized_eq_impl

@[noinline] def wrappedInsert (s : SetWithoutValArray Nat) (key : Nat) : SetWithoutValArray Nat :=
  s.insert key

@[noinline] def rawInsert (s : SetWithoutValArray.Raw.SizedRaw Nat) (key : Nat) :
    SetWithoutValArray.Raw.SizedRaw Nat := SetWithoutValArray.Raw.insertSizedImpl s key

@[noinline] def wrappedContains (s : SetWithoutValArray Nat) (key : Nat) : Bool := s.contains key

@[noinline] def rawContains (s : SetWithoutValArray.Raw.SizedRaw Nat) (key : Nat) : Bool :=
  s.toRaw.contains key

@[noinline] def wrappedSize (s : SetWithoutValArray Nat) : Nat := s.size

@[noinline] def rawSize (s : SetWithoutValArray.Raw.SizedRaw Nat) : Nat := s.size

-- Compare exact bucket order and promotion shape, ignoring only values.
private partial def sameShape [BEq α]
    (a : Lean.PersistentHashMap.Node α Unit) (b : SetWithoutValArray.Node α) : Bool :=
  match a, b with
  | .collision keys _ _, .collision keys' => keys == keys'
  | .entries es, .entries es' => es.size == es'.size && (es.zip es').all fun (e, e') =>
    match e, e' with
    | .null, .null => true
    | .entry k _, .entry k' => k == k'
    | .ref n, .ref n' => sameShape n n'
    | _, _ => false
  | _, _ => false

private def check [BEq α] [LawfulBEq α] [Hashable α] (label : String)
    (set : SetWithoutValArray α) (reference : Set α) (bare : SetWithoutValArray.Raw α)
    (model queries : List α) : IO Nat := do
  let native := reference.toRaw
  unless sameShape native.set.root set.toRaw.root && sameShape native.set.root bare.root do
    throw <| IO.userError s!"{label}: tree shape differs from upstream"
  let keys := set.toList
  unless keys == reference.toList && keys == native.toList.reverse &&
      keys.length == model.length && keys.eraseDups.length == keys.length &&
      set.size == model.length && set.size == reference.size do
    throw <| IO.userError s!"{label}: enumeration, uniqueness, or cached size mismatch"
  let imported := SetWithoutValArray.ofRaw set.toRaw set.valid set.unique
  unless imported.size == set.size && imported.toList == keys do
    throw <| IO.userError s!"{label}: raw import mismatch"
  for key in queries do
    let expected := model.contains key
    unless set.contains key == expected && native.contains key == expected &&
        bare.contains key == expected && keys.contains key == expected &&
        decide (key ∈ set) == expected do
      throw <| IO.userError s!"{label}: lookup mismatch"
  return queries.length

private def sequence [BEq α] [LawfulBEq α] [Hashable α]
    (label : String) (keyOf : Nat → α) : IO Nat := do
  let mut set : SetWithoutValArray α := ∅
  let mut reference : Set α := ∅
  let mut bare : SetWithoutValArray.Raw α := ∅
  let mut model : List α := []
  let mut history := #[]
  let queries := (List.range 104).map keyOf
  let mut checks ← check label set reference bare model queries
  for step in [0:192] do
    history := history.push (set, reference, bare, model)
    let key := keyOf ((step * 37) % 96)
    set := set.insert key
    reference := reference.insert key
    bare := bare.insert key
    unless model.contains key do model := key :: model
    checks := checks + (← check s!"{label}/insert/{step}" set reference bare model queries)
  for (old, oldReference, oldBare, oldModel) in history do
    checks := checks + (← check s!"{label}/snapshot" old oldReference oldBare oldModel queries)
  return checks

-- The compiler rewrite is valid even without routing/equality invariants and
-- with a caller-supplied count. Check malformed nodes and the zero-level worker.
private def checkRawSized : IO Unit := do
  let raw : SetWithoutValArray.Raw Nat := ⟨.entries #[]⟩
  let result := SetWithoutValArray.Raw.insertSizedImpl ⟨raw, 10⟩ 5
  unless result.size == 11 && !result.toRaw.contains 5 do
    throw <| IO.userError "malformed-slot specification mismatch"
  let collision : SetWithoutValArray.Raw Nat := ⟨.collision #[1, 2, 3]⟩
  let old : SetWithoutValArray.Raw.SizedRaw Nat := ⟨collision, 10⟩
  for key in #[1, 4] do
    let res := SetWithoutValArray.Raw.insertSizedNoExpand old 0 key
    unless res.size == (if key == 1 then 10 else 11) && res.toRaw.contains key do
      throw <| IO.userError "zero-level collision size mismatch"

def run : IO Unit := do
  let mut checks := 0
  for (label, hashFn) in #[
      ("default", hash (α := Nat)), ("identity", Nat.toUInt64),
      ("prefix", fun n => n.toUInt64 <<< 15), ("collision", fun _ => 0),
      ("high-bits", fun n => n.toUInt64 <<< 60)] do
    let _ : Hashable Nat := ⟨hashFn⟩
    checks := checks + (← sequence label id)
  checks := checks + (← sequence "name" (fun n => Lean.Name.num `setWithoutVals n))
  checkRawSized
  IO.println s!"set without vals: {checks} query comparisons, cached counts, raw imports, shape, and snapshots passed."

end HAMTVerify.SetWithoutValArrayTests
