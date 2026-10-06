import VerifiedHAMT

/-! Kernel proofs and synthetic differential tests for value lookup. -/

namespace VerifiedHAMT.FindTests

open Lean.PersistentHashMap
open scoped VerifiedHAMT.Map

-- Generic values deliberately have neither BEq nor Inhabited instances.
example [BEq α] [LawfulBEq α] [Hashable α] (m : Map α β) (k : α) (v : β) :
    m.find? k = some v ↔ m.MapsTo k v := Map.find?_eq_some_iff m k v

example [BEq α] [LawfulBEq α] [Hashable α] (m : Map α β) (k q : α) (v : β) :
    (m.insert k v).find? q = if q == k then some v else m.find? q := by simp

example [BEq α] [LawfulBEq α] [Hashable α] (m : Map α β) (k q : α)
    (v : β) (hne : q ≠ k) : (m.insert k v).find? q = m.find? q := by simp [hne]

example [BEq α] [LawfulBEq α] [Hashable α] (m : Map α β) (k : α) (v w d : β) :
    ((m.insert k v).insert k w).findD k d = w := by simp

example : (Map.ofList [(1, 10), (2, 20), (1, 99)]).find? 1 = some 99 := by
  simp [Map.ofList]

example : (Map.ofList [(1, 10), (2, 20), (1, 99)]).find? 3 = none := by
  simp [Map.ofList]

example : (∅ : Map Nat (Option Nat)).find? 1 = none := by simp
example : ((∅ : Map Nat (Option Nat)).insert 1 none).find? 1 = some none := by simp

-- Std.HashMap exposes proved insertion equations, so unlike the opaque native
-- HAMT we can also check lookup equivalence for arbitrary finite input lists.
private theorem lookup_insertMany_eq_std [BEq α] [LawfulBEq α] [Hashable α]
    (bindings : List (α × β)) (map : Map α β) (std : Std.HashMap α β)
    (same : ∀ q, map.find? q = std.get? q) (key : α) :
    (bindings.foldl (fun m kv => m.insert kv.1 kv.2) map).find? key =
      (std.insertMany bindings).get? key := by
  induction bindings generalizing map std with
  | nil => simpa using same key
  | cons kv xs ih =>
    rw [List.foldl_cons, Std.HashMap.insertMany_cons]
    apply ih
    intro q
    rw [Map.find?_insert, Std.HashMap.get?_insert, BEq.comm (a := q) (b := kv.1), same q]

theorem ofList_lookup_eq_std [BEq α] [LawfulBEq α] [Hashable α]
    (bindings : List (α × β)) (key : α) :
    (Map.ofList bindings).find? key = (Std.HashMap.ofList bindings).get? key := by
  rw [Map.ofList, Std.HashMap.ofList_eq_insertMany_empty]
  apply lookup_insertMany_eq_std
  intro q
  change (∅ : Map α β).find? q = (∅ : Std.HashMap α β)[q]?
  simp

theorem ofList_findD_eq_std [BEq α] [LawfulBEq α] [Hashable α]
    (bindings : List (α × β)) (key : α) (fallback : β) :
    (Map.ofList bindings).findD key fallback = (Std.HashMap.ofList bindings).getD key fallback := by
  change ((Map.ofList bindings).find? key).getD fallback = _
  rw [ofList_lookup_eq_std]
  exact Std.HashMap.getD_eq_getD_getElem?.symm

-- The collision scan is total even for an empty or out-of-range suffix.
example : findCollisionAux #[2, 7] #[20, 70] rfl 2 7 = none := by
  rw [findCollisionAux]; simp
example : findCollisionAux #[2, 7] #[20, 70] rfl 100 7 = none := by
  rw [findCollisionAux]; simp
example : findNode (.collision (#[] : Array Nat) (#[] : Array Nat) rfl) 0 7 = none := by
  rw [findNode, findCollisionAux]; simp
example : findNode (.entries (#[] : Array (Entry Nat Nat (Node Nat Nat)))) 0 7 = none := by
  rw [findNode_entries]; simp

-- Valid permits duplicates. Lookup returns the first, while MapsTo includes both:
-- Unique really is needed for the converse in find?_eq_some_iff.
private def duplicates : Node Nat Nat := .collision #[2, 2] #[20, 21] rfl
example (hashAt : Nat → USize) : WellFormed hashAt duplicates := .collision _ _ _ _
example : HasBinding 2 21 duplicates := .collision (i := 1) (by decide) rfl rfl
example : findNode duplicates 0 2 = some 20 := by
  unfold duplicates
  rw [findNode, findCollisionAux]; simp

-- Without routing, a stored key can be missed.
private def misplaced : Node Nat Nat :=
  .entries (Array.replicate 32 .null |>.set 1 (.entry 7 70) (by decide))
example : HasBinding 7 70 misplaced := .entry (i := 1) (hi := by decide) (by simp)
example : findNode misplaced 0 7 = none := by
  unfold misplaced
  rw [findNode_entries]; simp

/-- info: 'VerifiedHAMT.findNode_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedHAMT.findNode_sound
/-- info: 'VerifiedHAMT.find?_eq_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedHAMT.find?_eq_some_iff
/-- info: 'VerifiedHAMT.find?_eq_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedHAMT.find?_eq_none_iff
/-- info: 'VerifiedHAMT.find?_isSome_eq_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedHAMT.find?_isSome_eq_contains
/-- info: 'VerifiedHAMT.Map.find?_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Map.find?_insert
/-- info: 'VerifiedHAMT.Map.findD_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Map.findD_insert
/-- info: 'VerifiedHAMT.FindTests.ofList_lookup_eq_std' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ofList_lookup_eq_std

private def modelFind [BEq α] (model : List (α × Nat)) (key : α) : Option Nat :=
  (model.find? (fun kv => key == kv.1)).map Prod.snd

private def checkQueries [BEq α] [LawfulBEq α] [Hashable α]
    (map : Map α Nat) (native : Lean.PersistentHashMap α Nat) (std : Std.HashMap α Nat)
    (model : List (α × Nat)) (makeKey : Nat → α) : IO Nat := do
  for id in [0:80] do
    let key := makeKey id
    let expected := modelFind model key
    unless map.find? key == expected && VerifiedHAMT.find? native key == expected &&
        native.find? key == expected && std.get? key == expected do
      throw <| IO.userError "find?: synthetic differential comparison failed"
    unless map.findD key 1234567 == expected.getD 1234567 &&
        native.findD key 1234567 == expected.getD 1234567 &&
        std.getD key 1234567 == expected.getD 1234567 &&
        (map.find? key).isSome == map.contains key do
      throw <| IO.userError "findD/contains: synthetic differential comparison failed"
  return 80

private def checkSequence [BEq α] [LawfulBEq α] [Hashable α]
    (makeKey : Nat → α) : IO Nat := do
  let mut map : Map α Nat := ∅
  let mut native : Lean.PersistentHashMap α Nat := {}
  let mut std : Std.HashMap α Nat := ∅
  let mut model : List (α × Nat) := []
  let mut checks ← checkQueries map native std model makeKey
  let mut snapshots := #[(map, native, std, model)]
  for step in [0:96] do
    let id := (step * 37) % 64
    let key := makeKey id
    -- Overwrites, including a zero value, catch key/value misalignment.
    let value := if step % 7 == 0 then 0 else step * 17 + 3
    map := map.insert key value
    native := native.insert key value
    std := std.insert key value
    model := (key, value) :: model.filter (fun kv => kv.1 != key)
    checks := checks + (← checkQueries map native std model makeKey)
    if step % 8 == 0 then snapshots := snapshots.push (map, native, std, model)
  for (oldMap, oldNative, oldStd, oldModel) in snapshots do
    checks := checks + (← checkQueries oldMap oldNative oldStd oldModel makeKey)
  -- Raw lookup remains testable after upstream deletion. This does not prove erase.
  for step in [0:80] do
    let key := makeKey ((step * 37) % 80)
    native := native.erase key
    std := std.erase key
    model := model.filter (fun kv => kv.1 != key)
    for id in [0:80] do
      let q := makeKey id
      let expected := modelFind model q
      unless VerifiedHAMT.find? native q == expected && native.find? q == expected &&
          std.get? q == expected do
        throw <| IO.userError "find?: synthetic post-erase comparison failed"
      checks := checks + 1
  return checks

-- Existing trees can be deeper than the insertion promotion limit.
private def deepNode : Nat → Node Nat Nat
  | 0 => .collision #[7] #[70] rfl
  | n + 1 => .entries (Array.replicate 32 .null |>.set 0 (.ref (deepNode n)) (by decide))

def run : IO Unit := do
  let mut checks := 0
  for hashFn in #[hash, Nat.toUInt64, (fun n => mixHash 0x5eed n.toUInt64),
      (fun n => n.toUInt64 <<< 15), (fun _ => 0), (fun n => n.toUInt64 <<< 60)] do
    let _ : Hashable Nat := ⟨hashFn⟩
    checks := checks + (← checkSequence (fun n : Nat => n))
  checks := checks + (← checkSequence (fun n => Lean.Name.num (.str .anonymous "synthetic") n))
  unless findNode (deepNode 12) 0 7 == some 70 && findNode (deepNode 12) 0 8 == none do
    throw <| IO.userError "find?: deep synthetic tree failed"
  let nested := (∅ : Map Nat (Option Nat)).insert 1 none |>.insert 2 (some 0)
  unless nested.find? 1 == some none && nested.find? 2 == some (some 0) &&
      nested.find? 3 == none do
    throw <| IO.userError "find?: nested option value failed"
  IO.println s!"find?: {checks} synthetic query checks passed (verified, native HAMT, Std.HashMap, list model); collisions, overwrites, snapshots, deep trees, nested values."

end VerifiedHAMT.FindTests
