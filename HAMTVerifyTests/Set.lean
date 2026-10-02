import HAMTVerify.Set

/-! Set API examples and regression tests using its scoped simplification rules. -/

namespace HAMTVerify.SetTests

open scoped HAMTVerify.Set

example [BEq α] [LawfulBEq α] [Hashable α] (set : Set α) (key : α) :
    set.contains key = true ↔ key ∈ set := Set.contains_eq_true_iff set key

example [BEq α] [LawfulBEq α] [Hashable α] (set : Set α) (key q : α) :
    q ∈ set.insert key ↔ q = key ∨ q ∈ set := by simp

example [BEq α] [LawfulBEq α] [Hashable α] (set : Set α) (key q : α) :
    q ∈ (set.insert key).insert key ↔ q ∈ set.insert key := by simp

example [BEq α] [LawfulBEq α] [Hashable α] (keys : List α) (key : α) :
    key ∈ Set.ofList keys ↔ key ∈ keys := by simp

example [BEq α] [LawfulBEq α] [Hashable α] (keys : List α) (key : α) :
    (Set.ofList keys).contains key = keys.contains key := by simp

example [BEq α] [LawfulBEq α] [Hashable α] (key q : α) :
    q ∈ ({key} : Set α) ↔ q = key := by simp

example : 7 ∈ Set.ofList [7, 3, 7] := by simp
example : 9 ∉ Set.ofList [7, 3, 7] := by simp

-- Both representation bridges keep the original data and its invariant proofs.
example [BEq α] [Hashable α] (map : Map α Unit) :
    (Set.ofMap map).toMap = map := by simp

example [BEq α] [Hashable α] (set : Set α) :
    Set.ofRaw set.toRaw set.toMap.valid set.toMap.unique = set := by simp

example (raw : Lean.PersistentHashSet Nat) (hv : Valid raw.set) (hu : Unique raw.set.root) :
    (Set.ofRaw raw hv hu).toRaw = raw := by simp

#guard ({1, 2, 1} : Set Nat).contains 2
#guard decide (2 ∈ ({1, 2, 1} : Set Nat))
#guard !decide (3 ∈ ({1, 2, 1} : Set Nat))
#guard !(∅ : Set Nat).contains 0

/-- info: 'HAMTVerify.Set.contains_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Set.contains_eq_true_iff
/-- info: 'HAMTVerify.Set.mem_insert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Set.mem_insert_iff
/-- info: 'HAMTVerify.Set.mem_ofList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Set.mem_ofList

-- Paired entry points compare the wrapper to our verified map operations on
-- the native set representation, not to upstream's opaque partial constants.
@[noinline] def wrappedInsert (set : Set Nat) (key : Nat) : Set Nat := set.insert key

@[noinline] def rawInsert (set : Lean.PersistentHashSet Nat) (key : Nat) :
    Lean.PersistentHashSet Nat := ⟨HAMTVerify.insert set.set key ()⟩

@[noinline] def wrappedContains (set : Set Nat) (key : Nat) : Bool := set.contains key

@[noinline] def rawContains (set : Lean.PersistentHashSet Nat) (key : Nat) : Bool :=
  HAMTVerify.contains set.set key

private def checkSequence [BEq α] [LawfulBEq α] [Hashable α]
    (label : String) (keyOf : Nat → α) : IO Nat := do
  let mut set : Set α := ∅
  let mut native : Lean.PersistentHashSet α := ∅
  let mut model : List α := []
  let queries := (List.range 104).map keyOf
  let mut checks := 0
  -- The first pass inserts distinct keys; the second pass inserts duplicates.
  for step in [0:192] do
    let key := keyOf ((step * 37) % 96)
    let old := set
    let oldModel := model
    set := set.insert key
    native := native.insert key
    model := key :: model
    for q in queries do
      let expected := model.contains q
      unless set.contains q == expected && native.contains q == expected &&
          decide (q ∈ set) == expected && old.contains q == oldModel.contains q do
        throw <| IO.userError s!"{label}: set insertion, duplicate, or snapshot mismatch"
      checks := checks + 1
  let bulk := Set.ofList model
  let imported := Set.ofRaw set.toRaw set.toMap.valid set.toMap.unique
  for q in queries do
    unless bulk.contains q == model.contains q && imported.contains q == model.contains q do
      throw <| IO.userError s!"{label}: set bulk construction or import mismatch"
    checks := checks + 1
  return checks

private def checkNat (label : String) (hashFn : Nat → UInt64) : IO Nat := do
  let _ : Hashable Nat := ⟨hashFn⟩
  checkSequence label id

def run : IO Unit := do
  let mut checks ← checkNat "default" hash
  checks := checks + (← checkNat "shared-prefix" (fun n => n.toUInt64 <<< 15))
  checks := checks + (← checkNat "collisions" (fun _ => 0))
  checks := checks + (← checkSequence "names" (fun n => Lean.Name.num (.str .anonymous "set") n))
  IO.println s!"set: {checks} comparisons passed, including duplicates, snapshots, bulk construction, and imports."

end HAMTVerify.SetTests
