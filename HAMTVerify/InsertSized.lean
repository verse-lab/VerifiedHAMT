module

public import HAMTVerify.InsertCachedProofs
import all Init.Data.Array.Basic
import all Lean.Data.PersistentHashMap

@[expose] public section

/-!
Insertion with a cached count, following the tree-map pattern of returning the
updated runtime data together with its size. The native HAMT has no subtree-size
fields, so a single `SizedRaw` container carries the total count down the route
and is reused while reconstructing the parents. Proofs are separate and erased.
-/

namespace HAMTVerify

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

/-- Runtime data shared by the insertion traversal and the bundled map. During
descent `size` is the whole map's count, not the current child's count. Keeping
both fields in one consumed container allows the compiler to reuse it throughout
the traversal, instead of allocating a membership result at each level. -/
structure SizedRaw (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  /-- The native map, or the child currently being updated during insertion. -/
  toRaw : Lean.PersistentHashMap α β
  /-- The total map size. `Map` additionally proves that this counts its keys. -/
  size : Nat

/-- Update the count at the insertion site, continuing through existing nodes
even after the promotion limit. Reconstruct each parent directly in its branch
so the compiler can reuse both its constructor and the size container. -/
def insertSizedNoExpand [BEq α] [Hashable α] (s : SizedRaw α β) (h : USize)
    (key : α) (value : β) : SizedRaw α β :=
  let ⟨⟨node⟩, size⟩ := s
  match node with
  | .collision keys vals hsz =>
    let oldSize := keys.size
    let b := insertCollision ⟨.collision keys vals hsz, .mk ..⟩ 0 key value
    let size := if getCollisionNodeSize b == oldSize then size else size + 1
    ⟨⟨b.val⟩, size⟩
  | .entries es =>
    let i := slot h
    if hi : i < es.size then
      let old := es[i]
      let es' := es.set i .null
      match he : old with
      | .null => ⟨⟨.entries (es'.set i (.entry key value) (by simpa [es'] using hi))⟩, size + 1⟩
      | .entry k v =>
        if key == k then
          ⟨⟨.entries (es'.set i (.entry key value) (by simpa [es'] using hi))⟩, size⟩
        else
          ⟨⟨.entries (es'.set i (.ref (mkCollisionNode k v key value))
            (by simpa [es'] using hi))⟩, size + 1⟩
      | .ref child =>
        let result := insertSizedNoExpand ⟨⟨child⟩, size⟩ (nextHash h) key value
        ⟨⟨.entries (es'.set i (.ref result.toRaw.root) (by simpa [es'] using hi))⟩, result.size⟩
    -- Match the membership-based specification on malformed short arrays too.
    -- Bundled maps rule this case out through their routing invariant.
    else ⟨⟨.entries es⟩, size + 1⟩
termination_by sizeOf s.toRaw.root
decreasing_by
  have hs := Array.sizeOf_get es i hi
  change es[i] = .ref child at he
  rw [he] at hs
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
      let i := slot h
      if hi : i < es.size then
        let old := es[i]
        let es' := es.set i .null
        match old with
        | .null => ⟨⟨.entries (es'.set i (.entry key value) (by simpa [es'] using hi))⟩, size + 1⟩
        | .entry k v =>
          if key == k then
            ⟨⟨.entries (es'.set i (.entry key value) (by simpa [es'] using hi))⟩, size⟩
          else
            ⟨⟨.entries (es'.set i (.ref (mkCollisionNode k v key value))
              (by simpa [es'] using hi))⟩, size + 1⟩
        | .ref child =>
          let result := insertSizedRaw levels (offset + shift) ⟨⟨child⟩, size⟩
            (nextHash h) key value
          ⟨⟨.entries (es'.set i (.ref result.toRaw.root) (by simpa [es'] using hi))⟩, result.size⟩
      else ⟨⟨.entries es⟩, size + 1⟩
    | .collision keys vals hsz =>
      let oldSize := keys.size
      let b := insertCollision ⟨.collision keys vals hsz, .mk ..⟩ 0 key value
      let size := if getCollisionNodeSize b == oldSize then size else size + 1
      match b with
      | ⟨.collision keys vals hsz, _⟩ =>
        if keys.size < maxCollisions then ⟨⟨b.val⟩, size⟩
        else ⟨⟨.entries (rebuildCached (insertNodeCached levels (offset + shift))
          offset ⟨keys, vals, hsz⟩ 0 mkEmptyEntriesArray)⟩, size⟩
      | ⟨.entries _, h⟩ => nomatch h

/-- Executable insertion with a size accumulator. -/
@[inline] def insertSizedImpl [BEq α] [Hashable α] (s : SizedRaw α β)
    (key : α) (value : β) : SizedRaw α β :=
  insertSizedRaw (maxDepth.toNat - 1) 0 s (hash key).toUSize key value

theorem insertAt_size [BEq α] (b : Bucket α β) (i : Nat) (key : α) (value : β) :
    (insertAt b i key value).keys.size =
      if containsAt b.keys i key then b.keys.size else b.keys.size + 1 := by
  rw [insertAt, containsAt]
  split
  · split
    · simp
    · exact insertAt_size b (i + 1) key value
  · simp
termination_by b.keys.size - i

@[scoped simp] theorem insertCollision_size_eq [BEq α] (keys : Array α) (vals : Array β)
    (hsz : keys.size = vals.size) (key : α) (value : β) :
    (getCollisionNodeSize (insertCollision ⟨.collision keys vals hsz, .mk ..⟩ 0 key value)
      == keys.size) = containsAt keys 0 key := by
  rw [insertCollision_eq ⟨keys, vals, hsz⟩]
  simp only [Bucket.node, getCollisionNodeSize, insertAt_size]
  cases containsAt keys 0 key <;> simp

theorem insertSizedNoExpand_eq [BEq α] [Hashable α] (s : SizedRaw α β) (h : USize)
    (key : α) (value : β) :
    insertSizedNoExpand s h key value =
      ⟨⟨insertNoExpand s.toRaw.root h key value⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by
  obtain ⟨⟨node⟩, size⟩ := s
  cases node with
  | collision keys vals hsz =>
    simp only [insertSizedNoExpand, insertNoExpand, containsNode, insertCollision_size_eq]
  | entries es =>
    rw [insertSizedNoExpand, containsNode_entries, insertNoExpand]
    split
    · rename_i hi
      cases he : es[slot h] with
      | null => simp
      | entry k v => cases hk : key == k <;> simp [hk]
      | ref child =>
        dsimp only
        rw [insertSizedNoExpand_eq ⟨⟨child⟩, size⟩ (nextHash h) key value]
    · rfl
termination_by sizeOf s.toRaw.root
decreasing_by
  have hs := Array.sizeOf_get es (slot h) (by assumption)
  rw [he] at hs
  simp at hs ⊢
  omega

theorem insertSizedRaw_eq [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (s : SizedRaw α β) (h : USize) (key : α) (value : β) :
    insertSizedRaw levels offset s h key value =
      ⟨⟨insertNodeCached levels offset s.toRaw.root h key value⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by
  induction levels generalizing offset s h key value with
  | zero => exact insertSizedNoExpand_eq s h key value
  | succ levels ih =>
    obtain ⟨⟨node⟩, size⟩ := s
    cases node with
    | entries es =>
      simp only [insertSizedRaw, insertNodeCached, insertEntriesCached,
        Array.modify, Array.modifyM, containsNode_entries]
      split
      · rename_i hi
        cases he : es[slot h] with
        | null => simp
        | entry k v => cases hk : key == k <;> simp [hk]
        | ref child => simp [ih]
      · rfl
    | collision keys vals hsz =>
      simp only [insertSizedRaw, insertNodeCached, containsNode, insertCollision_size_eq]
      generalize insertCollision ⟨Node.collision keys vals hsz, IsCollisionNode.mk ..⟩ 0 key value = b
      obtain ⟨b, hb⟩ := b
      cases hb
      dsimp only
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
