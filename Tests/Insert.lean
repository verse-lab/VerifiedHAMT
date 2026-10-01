import HAMTVerify

/-! Kernel-checked update laws and executable insertion comparisons.
The upstream lookups and structural comparator below are used only in regression tests.
-/

namespace HAMTVerify.InsertTests

open Lean.PersistentHashMap

example [BEq α] [LawfulBEq α] [Hashable α] (m : Lean.PersistentHashMap α β)
    (h : Valid m) (k q : α) (v : β) :
    contains (insert m k v) q = ((q == k) || contains m q) := contains_insert m h k q v

example [BEq α] [LawfulBEq α] [Hashable α] (k : α) (v₁ v₂ w : β) :
    MapsTo k w (insert (insert Lean.PersistentHashMap.empty k v₁) k v₂) ↔ w = v₂ := by
  apply mapsTo_insert_self
  · exact valid_insert _ valid_empty _ _
  · exact unique_insert _ valid_empty unique_empty _ _

example [BEq α] [LawfulBEq α] [Hashable α] (bindings : List (α × β)) :
    Valid (bindings.foldl (fun m kv => insert m kv.1 kv.2) Lean.PersistentHashMap.empty) :=
  (insert_fold_valid_unique bindings).1

-- Valid alone permits duplicate keys; the update law states its extra premise.
private def duplicates : Node Nat Nat := .collision #[2, 2] #[20, 21] rfl

example (hashAt : Nat → USize) : WellFormed hashAt duplicates := .collision _ _ _ _

example : ¬ Unique duplicates := by
  intro h
  cases h with
  | collision distinct => have h := distinct 0 (by decide) 1 (by decide) rfl; omega

-- An empty or too-short entries array is left unchanged, as by upstream modify.
-- The successful insertion guarantees require Valid and cannot cover this node.
example : insertNode 6 (fun _ : Nat => 0) (.entries #[]) 7 70 = .entries #[] := by
  simp [insertNode, insertEntries]

-- Neither a depth-limit collision nor the key/value arrays require Inhabited β.
example [BEq α] [LawfulBEq α] (k : α) (v : β) (hashAt : α → USize) :
    Updated (Node.collision (#[] : Array α) (#[] : Array β) rfl)
      (insertNode 0 hashAt (.collision (#[] : Array α) (#[] : Array β) rfl) k v) k v := by
  apply (insertNode_unique_updated 0 hashAt _ (.collision _ _ _ _) _ k v).2
  exact .collision (by intro i hi; simp at hi)

/-- info: 'HAMTVerify.valid_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HAMTVerify.valid_insert
/-- info: 'HAMTVerify.mem_insert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HAMTVerify.mem_insert_iff
/-- info: 'HAMTVerify.unique_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HAMTVerify.unique_insert
/-- info: 'HAMTVerify.mapsTo_insert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HAMTVerify.mapsTo_insert_iff
/-- info: 'HAMTVerify.contains_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HAMTVerify.contains_insert
/-- info: 'HAMTVerify.insert_fold_valid_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HAMTVerify.insert_fold_valid_unique

-- Compare the complete representation as well as observational behavior.
-- This partial test oracle is deliberately outside the verified implementation.
private partial def sameNode [BEq α] [BEq β] : Node α β → Node α β → Bool
  | .collision ks vs _, .collision ks' vs' _ => ks == ks' && vs == vs'
  | .entries es, .entries es' =>
    es.size == es'.size && (es.toList.zip es'.toList).all fun (e, e') =>
      match e, e' with
      | .null, .null => true
      | .entry k v, .entry k' v' => k == k' && v == v'
      | .ref n, .ref n' => sameNode n n'
      | _, _ => false
  | _, _ => false

private def modelFind [BEq α] (key : α) (model : List (α × Nat)) : Option Nat :=
  (model.find? (fun kv => key == kv.1)).map Prod.snd

private def checkMaps [BEq α] [Hashable α] (label : String)
    (total native : Lean.PersistentHashMap α Nat) (model : List (α × Nat))
    (queries : Array α) : IO Nat := do
  unless sameNode total.root native.root do
    throw <| IO.userError s!"{label}: node representations differ"
  for q in queries do
    let expected := modelFind q model
    let t := total.find? q
    let n := native.find? q
    let found := HAMTVerify.contains total q
    unless t == expected && n == expected && found == expected.isSome do
      throw <| IO.userError s!"{label}: total={t}, upstream={n}, expected={expected}, contains={found}"
  return queries.size

private def checkSequence [BEq α] [Hashable α] (label : String) (makeKey : Nat → α) : IO Nat := do
  let queries := (List.range 112).toArray.map makeKey
  let mut total : Lean.PersistentHashMap α Nat := {}
  let mut native : Lean.PersistentHashMap α Nat := {}
  let mut model : List (α × Nat) := []
  let mut checks ← checkMaps s!"{label}/empty" total native model queries
  for step in [0:96] do
    let key := makeKey ((step * 37) % 96)
    let value := step + 100
    let oldTotal := total
    let oldNative := native
    let oldModel := model
    total := HAMTVerify.insert total key value
    native := native.insert key value
    model := (key, value) :: model.filter (fun kv => !(kv.1 == key))
    checks := checks + (← checkMaps s!"{label}/insert/{step}" total native model queries)
    checks := checks + (← checkMaps s!"{label}/snapshot/{step}" oldTotal oldNative oldModel queries)
  -- Several overwrites per key, including zero values, after all promotions.
  for step in [0:192] do
    let key := makeKey ((step * 53) % 96)
    let value := step % 17
    total := HAMTVerify.insert total key value
    native := native.insert key value
    model := (key, value) :: model.filter (fun kv => !(kv.1 == key))
    checks := checks + (← checkMaps s!"{label}/replace/{step}" total native model queries)
  return checks

private def checkNat (label : String) (hashFn : Nat → UInt64) : IO Nat := do
  let _ : Hashable Nat := ⟨hashFn⟩
  checkSequence label id

private def checkPromotionBoundaries : IO Unit := do
  -- Force one root slot, then split at the next level. The fourth key promotes
  -- the three-key child bucket, and the fifth updates the resulting entries.
  let _ : Hashable Nat := ⟨fun n => n.toUInt64 <<< 5⟩
  let mut total : Lean.PersistentHashMap Nat Nat := {}
  let mut native : Lean.PersistentHashMap Nat Nat := {}
  for k in [0:5] do
    total := HAMTVerify.insert total k (k + 10)
    native := native.insert k (k + 10)
    unless sameNode total.root native.root do throw <| IO.userError "promotion boundary mismatch"
    let expectedPromotion := k >= 3
    let promoted := match total.root with
      | .entries es => match es[0]! with | .ref (.entries _) => true | _ => false
      | _ => false
    unless promoted == expectedPromotion do throw <| IO.userError "unexpected bucket promotion threshold"
  -- A duplicate-key bucket is Valid but not Unique. Promotion can make a later
  -- duplicate overwrite an earlier value, motivating the theorem's premise.
  let duplicateMap : Lean.PersistentHashMap Nat Nat :=
    ⟨.collision #[2, 7, 2, 8] #[20, 70, 21, 80] rfl⟩
  let dupTotal := HAMTVerify.insert duplicateMap 2 99
  let dupNative := duplicateMap.insert 2 99
  unless sameNode dupTotal.root dupNative.root && dupTotal.find? 2 == some 21 do
    throw <| IO.userError "duplicate-key promotion behavior changed"

private def checkManualNodes : IO Nat := do
  let _ : Hashable Nat := ⟨fun _ => 0⟩
  let queries := (List.range 80).toArray
  let mut checks := 0
  -- Well-formed root buckets are permitted even when not produced by insertion.
  for size in #[0, 1, 3, 4, 8, 64] do
    let keys := (List.range size).toArray
    let vals := keys.map (· + 100)
    let initial : Lean.PersistentHashMap Nat Nat :=
      ⟨.collision keys vals (by simp [vals])⟩
    let mut total := initial
    let mut native := initial
    let mut model := (List.range size).map (fun k => (k, k + 100))
    for key in #[0, size, size / 2, size + 1] do
      total := HAMTVerify.insert total key 999
      native := native.insert key 999
      model := (key, 999) :: model.filter (fun kv => kv.1 != key)
      checks := checks + (← checkMaps s!"manual-bucket/{size}/{key}" total native model queries)
  -- Existing trees can be deeper than the promotion limit. At zero remaining
  -- promotion levels, insertion must still descend all the way to the bucket.
  let mut node : Node Nat Nat := .collision #[1] #[10] rfl
  for _ in [0:12] do
    node := .entries (mkEmptyEntriesArray.set 0 (.ref node)
      (by simpa [mkEmptyEntriesArray] using slot_lt_branching 0))
  let initial : Lean.PersistentHashMap Nat Nat := ⟨node⟩
  checks := checks + (← checkMaps "deep-existing-tree"
    (HAMTVerify.insert initial 2 20) (initial.insert 2 20) [(1, 10), (2, 20)] queries)
  return checks

def run : IO Unit := do
  checkPromotionBoundaries
  let mut checks ← checkManualNodes
  checks := checks + (← checkNat "default" hash)
  checks := checks + (← checkNat "mixed" (fun n => mixHash 20261001 n.toUInt64))
  checks := checks + (← checkNat "shared-prefix" (fun n => n.toUInt64 <<< 15))
  checks := checks + (← checkNat "constant" (fun _ => 0))
  checks := checks + (← checkNat "high-bits" (fun n => n.toUInt64 <<< 60))
  checks := checks + (← checkSequence "names" (fun n => Lean.Name.num (.str .anonymous "insert") n))
  IO.println s!"insert: {checks} query comparisons passed, with complete node comparisons, promotion boundaries, and snapshots."

end HAMTVerify.InsertTests
