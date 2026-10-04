module

public import HAMTVerify.SetWithoutValArray.Insert
import all Init.Data.Array.Basic

@[expose] public section

/-!
Insertion with a cached count, adapted from HAMTVerify.InsertSized by returning the
updated runtime data together with its size. The native HAMT has no subtree-size
fields, so `SizedRaw` carries the total count down the route and back through
the reconstructed parents. Proofs are separate and erased.
-/

namespace HAMTVerify.SetWithoutValArray.Raw

open Lean.PersistentHashMap (shift maxDepth maxCollisions)

variable {α : Type u}

/-- Runtime data shared by the insertion traversal and the bundled set. During
descent `size` is the whole set's count, not the current child's count. The
traversal returns this count together with the updated node, without returning
a separate membership result at each level. -/
structure SizedRaw (α : Type u) [BEq α] [Hashable α] where
  /-- The keys-only set, or the child currently being updated during insertion. -/
  toRaw : Raw α
  /-- Total set size. The public set additionally proves this counts its keys. -/
  size : Nat

/-- Update one slot, threading the total set size through the child callback. -/
@[inline] def insertSizedEntries [BEq α] [Hashable α]
    (es : Array (Entry α (Node α))) (size : Nat)
    (childInsert : (child : Node α) → .ref child ∈ es →
      Nat → USize → α → SizedRaw α)
    (h : USize) (key : α) : SizedRaw α :=
  let i := slot h
  if hi : i < es.size then
    let old := es[i]
    -- NOTE: As in `insertEntries`, clear the slot before the recursive call and
    -- write every arm into the cleared array, so that an unshared child is updated
    -- in place. The size travels back with the child's result.
    let es' := es.set i .null
    have hi' : i < es'.size := by simpa [es'] using hi
    match he : old with
    | .null => ⟨⟨.entries (es'.set i (.entry key) hi')⟩, size + 1⟩
    | .entry k =>
      if key == k then ⟨⟨.entries (es'.set i (.entry key) hi')⟩, size⟩
      else ⟨⟨.entries (es'.set i (.ref (mkCollisionNode k key)) hi')⟩, size + 1⟩
    | .ref child =>
      let result := childInsert child (he ▸ Array.getElem_mem hi) size (nextHash h) key
      ⟨⟨.entries (es'.set i (.ref result.toRaw.root) hi')⟩, result.size⟩
  -- The reference lookup returns false for an invalid slot; preserve its
  -- size specification even though the entries array is left unchanged.
  else ⟨⟨.entries es⟩, size + 1⟩

/-- Update the count at the insertion site, continuing through existing nodes
even after the promotion limit. The entries helper reconstructs the parent
and passes back the count returned by the child. -/
def insertSizedNoExpand [BEq α] [Hashable α] (s : SizedRaw α) (h : USize)
    (key : α) : SizedRaw α :=
  let ⟨⟨node⟩, size⟩ := s
  match node with
  | .collision keys =>
    let oldSize := keys.size
    let b := insertCollisionAux ⟨.collision keys, .mk ..⟩ 0 key
    let size := if getCollisionNodeSize b == oldSize then size else size + 1
    ⟨⟨b.val⟩, size⟩
  | .entries es =>
    insertSizedEntries es size (fun child _ size =>
      insertSizedNoExpand ⟨⟨child⟩, size⟩) h key
termination_by sizeOf s.toRaw.root
decreasing_by
  have hs := Array.sizeOf_lt_of_mem ‹_›
  simp at hs ⊢
  omega

/-- A cached-hash insertion carrying the total size in a reusable container.
Promotion rebuilds use the original insertion because the size change has already
been determined at the collision bucket. -/
def insertSizedRaw [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (s : SizedRaw α) (h : USize) (key : α) : SizedRaw α :=
  match levels with
  | 0 => insertSizedNoExpand s h key
  | levels + 1 =>
    let ⟨⟨node⟩, size⟩ := s
    match node with
    | .entries es =>
      insertSizedEntries es size (fun child _ size =>
        insertSizedRaw levels (offset + shift) ⟨⟨child⟩, size⟩) h key
    | .collision keys =>
      let oldSize := keys.size
      let b := insertCollision keys key
      let size := if getCollisionNodeSize b == oldSize then size else size + 1
      if getCollisionNodeSize b < maxCollisions then ⟨⟨b.val⟩, size⟩
      else ⟨⟨.entries (rebuild (insertNode levels (offset + shift))
        offset b 0 mkEmptyEntriesArray)⟩, size⟩

/-- Executable insertion with a size accumulator. -/
@[inline] def insertSizedImpl [BEq α] [Hashable α] (s : SizedRaw α)
    (key : α) : SizedRaw α :=
  insertSizedRaw (maxDepth.toNat - 1) 0 s (hash key).toUSize key

theorem insertCollisionAux_size [BEq α] (keys : Array α) (i : Nat) (key : α) :
    getCollisionNodeSize (insertCollisionAux ⟨.collision keys, .mk ..⟩ i key) =
      if (keys.drop i).contains key then keys.size else keys.size + 1 := by
  rw [insertCollisionAux.eq_def]
  dsimp only
  split
  · rename_i hi
    have step : (keys.drop i).contains key =
        ((key == keys[i]) || (keys.drop (i + 1)).contains key) := by
      have contains_drop (j : Nat) :
          (keys.drop j).contains key = (keys.toList.drop j).contains key := by
        simpa only [List.toArray_drop, Array.toArray_toList] using
          (List.contains_toArray (l := keys.toList.drop j) (a := key))
      simp only [contains_drop]
      have hs := congrArg (fun xs : List α => xs.contains key)
        (List.drop_eq_getElem_cons (l := keys.toList) (i := i) (by simpa using hi))
      simp only [List.contains_cons] at hs
      rw [Array.getElem_toList] at hs
      exact hs
    rw [step]
    split
    · simp_all [getCollisionNodeSize]
    · rename_i hk
      simpa [hk] using insertCollisionAux_size keys (i + 1) key
  · rename_i hi
    simp [getCollisionNodeSize, Array.extract_empty_of_size_le_start (by omega : keys.size ≤ i)]
termination_by keys.size - i

@[scoped simp] theorem insertCollision_size_eq [BEq α] (keys : Array α) (key : α) :
    (getCollisionNodeSize (insertCollision keys key) == keys.size) = keys.contains key := by
  rw [insertCollision, insertCollisionAux_size]
  simp only [Array.drop_eq_extract, Array.extract_size]
  cases keys.contains key <;> simp

theorem insertSizedEntries_eq [BEq α] [Hashable α]
    (es : Array (Entry α (Node α))) (size : Nat)
    (childInsert : (child : Node α) → .ref child ∈ es →
      Nat → USize → α → SizedRaw α)
    (childModel : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (h : USize) (key : α)
    (childSpec : ∀ child hmem,
      childInsert child hmem size (nextHash h) key =
        ⟨⟨childModel child hmem (nextHash h) key⟩,
          if containsNode child (nextHash h) key then size else size + 1⟩) :
    insertSizedEntries es size childInsert h key =
      ⟨⟨.entries (insertEntries es childModel h key)⟩,
        if containsNode (.entries es) h key then size else size + 1⟩ := by
  simp only [insertSizedEntries, insertEntries, containsNode_entries]
  split <;> grind

theorem insertSizedNoExpand_eq [BEq α] [Hashable α] (s : SizedRaw α) (h : USize)
    (key : α) :
    insertSizedNoExpand s h key =
      ⟨⟨insertNoExpand s.toRaw.root h key⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by
  obtain ⟨⟨node⟩, size⟩ := s
  cases node with
  | collision keys =>
    simp only [insertSizedNoExpand.eq_def, insertNoExpand.eq_def, containsNode,
      ← insertCollision.eq_def, insertCollision_size_eq]
  | entries es =>
    rw [insertSizedNoExpand.eq_def, insertNoExpand.eq_def]
    apply insertSizedEntries_eq
    intro child hmem
    exact insertSizedNoExpand_eq ⟨⟨child⟩, size⟩ (nextHash h) key
termination_by sizeOf s.toRaw.root
decreasing_by
  have hs := Array.sizeOf_lt_of_mem hmem
  simp at hs ⊢
  omega

theorem insertSizedRaw_eq [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (s : SizedRaw α) (h : USize) (key : α) :
    insertSizedRaw levels offset s h key =
      ⟨⟨insertNode levels offset s.toRaw.root h key⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by
  induction levels generalizing offset s h key with
  | zero => exact insertSizedNoExpand_eq s h key
  | succ levels ih =>
    obtain ⟨⟨node⟩, size⟩ := s
    cases node with
    | entries es =>
      simp only [insertSizedRaw, insertNode]
      apply insertSizedEntries_eq
      intro child hmem
      exact ih (offset + shift) ⟨⟨child⟩, size⟩ (nextHash h) key
    | collision keys =>
      simp only [insertSizedRaw, insertNode, containsNode, insertCollision_size_eq]
      split <;> rfl

/-- A simple specification preserving the bundled API's definitional equalities.
The executable traversal updates the tree and count together. -/
def insertSized [BEq α] [Hashable α] (s : SizedRaw α)
    (key : α) : SizedRaw α :=
  ⟨insert s.toRaw key,
    if containsNode s.toRaw.root (hash key).toUSize key then s.size else s.size + 1⟩

@[csimp] theorem insertSized_eq_impl : @insertSized = @insertSizedImpl := by
  funext α _ _ s key
  simp only [insertSized, insertSizedImpl, insertSizedRaw_eq, insert]

end HAMTVerify.SetWithoutValArray.Raw
