module

public import HAMTVerify.Insert
import all Init.Data.Array.Basic
import all Lean.Data.PersistentHashMap

@[expose] public section

/-!
Insertion with a cached count, following the tree-map pattern of returning the
updated runtime data together with its size. The native HAMT has no subtree-size
fields, so `SizedRaw` carries the total count down the route and back through
the reconstructed parents. Proofs are separate and erased.
-/

namespace HAMTVerify

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

/-- Runtime data shared by the insertion traversal and the bundled map. During
descent `size` is the whole map's count, not the current child's count. The
traversal returns this count together with the updated node, without returning
a separate membership result at each level. -/
structure SizedRaw (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  /-- The native map, or the child currently being updated during insertion. -/
  toRaw : Lean.PersistentHashMap α β
  /-- The total map size. `Map` additionally proves that this counts its keys. -/
  size : Nat

/-- Update one slot, threading the total map size through the child callback. -/
@[inline] def insertSizedEntries [BEq α] [Hashable α]
    (es : Array (Entry α β (Node α β))) (size : Nat)
    (childInsert : (child : Node α β) → .ref child ∈ es →
      Nat → USize → α → β → SizedRaw α β)
    (h : USize) (key : α) (value : β) : SizedRaw α β :=
  -- NOTE: The pure modifier returns only the array, so the outer match keeps
  -- the updated size. In the ref case recursion finishes before replacement;
  -- the original slot still holds the child during that recursive call.
  if hi : slot h < es.size then
    let (entry, size) := match he : es[slot h] with
      | .null => (.entry key value, size + 1)
      | .entry k v =>
        if key == k then (.entry key value, size)
        else (.ref (mkCollisionNode k v key value), size + 1)
      | .ref child =>
        let result := childInsert child (he ▸ Array.getElem_mem hi) size (nextHash h) key value
        (.ref result.toRaw.root, result.size)
    ⟨⟨.entries (Array.modifyInBoundWithCallBackProof es (slot h) (fun _ _ => entry) hi)⟩, size⟩
  -- The reference lookup returns false for an invalid slot; preserve its
  -- size specification even though the entries array is left unchanged.
  else ⟨⟨.entries es⟩, size + 1⟩

/-- Update the count at the insertion site, continuing through existing nodes
even after the promotion limit. The entries helper reconstructs the parent
and passes back the count returned by the child. -/
def insertSizedNoExpand [BEq α] [Hashable α] (s : SizedRaw α β) (h : USize)
    (key : α) (value : β) : SizedRaw α β :=
  let ⟨⟨node⟩, size⟩ := s
  match node with
  | .collision keys vals hsz =>
    let oldSize := keys.size
    let b := insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ 0 key value
    let size := if getCollisionNodeSize b == oldSize then size else size + 1
    ⟨⟨b.val⟩, size⟩
  | .entries es =>
    insertSizedEntries es size (fun child _ size =>
      insertSizedNoExpand ⟨⟨child⟩, size⟩) h key value
termination_by sizeOf s.toRaw.root
decreasing_by
  have hs := Array.sizeOf_lt_of_mem ‹_›
  simp at hs ⊢
  omega

/-- A cached-hash insertion carrying the total size in a reusable container.
Promotion rebuilds use the original insertion because the size change has already
been determined at the collision bucket. -/
def insertSizedRaw [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (s : SizedRaw α β) (h : USize) (key : α) (value : β) : SizedRaw α β :=
  match levels with
  | 0 => insertSizedNoExpand s h key value
  | levels + 1 =>
    let ⟨⟨node⟩, size⟩ := s
    match node with
    | .entries es =>
      insertSizedEntries es size (fun child _ size =>
        insertSizedRaw levels (offset + shift) ⟨⟨child⟩, size⟩) h key value
    | .collision keys vals hsz =>
      let oldSize := keys.size
      let b := insertCollision keys vals hsz key value
      let size := if getCollisionNodeSize b == oldSize then size else size + 1
      if getCollisionNodeSize b < maxCollisions then ⟨⟨b.val⟩, size⟩
      else ⟨⟨.entries (rebuild (insertNode levels (offset + shift))
        offset b 0 mkEmptyEntriesArray)⟩, size⟩

/-- Executable insertion with a size accumulator. -/
@[inline] def insertSizedImpl [BEq α] [Hashable α] (s : SizedRaw α β)
    (key : α) (value : β) : SizedRaw α β :=
  insertSizedRaw (maxDepth.toNat - 1) 0 s (hash key).toUSize key value

-- FIXME: A bit too long
theorem insertCollisionAux_size [BEq α] (keys : Array α) (vals : Array β)
    (hsz : keys.size = vals.size) (i : Nat) (key : α) (value : β) :
    getCollisionNodeSize (insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ i key value) =
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
      simpa [hk] using insertCollisionAux_size keys vals hsz (i + 1) key value
  · rename_i hi
    simp [getCollisionNodeSize, Array.extract_empty_of_size_le_start (by omega : keys.size ≤ i)]
termination_by keys.size - i

@[scoped simp] theorem insertCollision_size_eq [BEq α] (keys : Array α) (vals : Array β)
    (hsz : keys.size = vals.size) (key : α) (value : β) :
    (getCollisionNodeSize (insertCollision keys vals hsz key value) == keys.size) = keys.contains key := by
  rw [insertCollision, insertCollisionAux_size]
  simp only [Array.drop_eq_extract, Array.extract_size]
  cases keys.contains key <;> simp

theorem insertSizedEntries_eq [BEq α] [Hashable α]
    (es : Array (Entry α β (Node α β))) (size : Nat)
    (childInsert : (child : Node α β) → .ref child ∈ es →
      Nat → USize → α → β → SizedRaw α β)
    (childModel : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (h : USize) (key : α) (value : β)
    (childSpec : ∀ child hmem,
      childInsert child hmem size (nextHash h) key value =
        ⟨⟨childModel child hmem (nextHash h) key value⟩,
          if containsNode child (nextHash h) key then size else size + 1⟩) :
    insertSizedEntries es size childInsert h key value =
      ⟨⟨.entries (insertEntries es childModel h key value)⟩,
        if containsNode (.entries es) h key then size else size + 1⟩ := by
  simp only [insertSizedEntries, insertEntries, Array.modifyWithCallBackProof,
    Array.modifyInBoundWithCallBackProof, containsNode_entries]
  split <;> grind

theorem insertSizedNoExpand_eq [BEq α] [Hashable α] (s : SizedRaw α β) (h : USize)
    (key : α) (value : β) :
    insertSizedNoExpand s h key value =
      ⟨⟨insertNoExpand s.toRaw.root h key value⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by
  obtain ⟨⟨node⟩, size⟩ := s
  cases node with
  | collision keys vals hsz =>
    simp only [insertSizedNoExpand.eq_def, insertNoExpand.eq_def, containsNode,
      ← insertCollision.eq_def, insertCollision_size_eq]
  | entries es =>
    rw [insertSizedNoExpand.eq_def, insertNoExpand.eq_def]
    apply insertSizedEntries_eq
    intro child hmem
    exact insertSizedNoExpand_eq ⟨⟨child⟩, size⟩ (nextHash h) key value
termination_by sizeOf s.toRaw.root
decreasing_by
  have hs := Array.sizeOf_lt_of_mem hmem
  simp at hs ⊢
  omega

theorem insertSizedRaw_eq [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (s : SizedRaw α β) (h : USize) (key : α) (value : β) :
    insertSizedRaw levels offset s h key value =
      ⟨⟨insertNode levels offset s.toRaw.root h key value⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by
  induction levels generalizing offset s h key value with
  | zero => exact insertSizedNoExpand_eq s h key value
  | succ levels ih =>
    obtain ⟨⟨node⟩, size⟩ := s
    cases node with
    | entries es =>
      simp only [insertSizedRaw, insertNode]
      apply insertSizedEntries_eq
      intro child hmem
      exact ih (offset + shift) ⟨⟨child⟩, size⟩ (nextHash h) key value
    | collision keys vals hsz =>
      simp only [insertSizedRaw, insertNode, containsNode, insertCollision_size_eq]
      split <;> rfl

/-- A simple specification preserving the bundled API's definitional equalities.
The executable traversal updates the tree and count together. -/
def insertSized [BEq α] [Hashable α] (s : SizedRaw α β)
    (key : α) (value : β) : SizedRaw α β :=
  ⟨insert s.toRaw key value,
    if containsNode s.toRaw.root (hash key).toUSize key then s.size else s.size + 1⟩

@[csimp] theorem insertSized_eq_impl : @insertSized = @insertSizedImpl := by
  funext α β _ _ s key value
  simp only [insertSized, insertSizedImpl, insertSizedRaw_eq, insert]

end HAMTVerify
