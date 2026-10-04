module

public import HAMTVerify.SetWithoutValArray.Contains

@[expose] public section

/-! Total insertion, including collision-bucket promotion at the native threshold. -/

namespace HAMTVerify.SetWithoutValArray.Raw

open Lean.PersistentHashMap (shift branching maxDepth maxCollisions)

variable {α : Type u}

-- Corresponding to `insertAtCollisionNodeAux`
/-- Replace the first matching key, or append when the scan reaches the end.
Scanning the collision node directly allows its constructor to be reused. -/
def insertCollisionAux [BEq α] (b : CollisionNode α) (i : Nat)
    (key : α) : CollisionNode α :=
  match b with
  | ⟨.collision keys, _⟩ =>
    if hi : i < keys.size then
      if key == keys[i] then
        ⟨.collision (keys.set i key), .mk ..⟩
      else insertCollisionAux b (i + 1) key
    else
      ⟨.collision (keys.push key), .mk ..⟩
  | ⟨.entries _, h⟩ => nomatch h
termination_by getCollisionNodeSize b - i
decreasing_by simp only [getCollisionNodeSize]; omega

@[inline] def insertCollision [BEq α] (keys : Array α)
    (key : α) : CollisionNode α :=
  insertCollisionAux ⟨.collision keys, .mk ..⟩ 0 key

-- The `Node.entries` branch of `insertAux`
/-- Entries update with an already computed hash. The child callback receives
proof that the child is referenced by the original entries array. -/
@[inline] def insertEntries [BEq α]
    (es : Array (Entry α (Node α)))
    -- NOTE: `insertEntries` handles the current level; `childInsert` handles the next level.
    -- Only the `.ref` case consumes another hash chunk and invokes the callback.
    (childInsert : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (h : USize) (key : α) :
    Array (Entry α (Node α)) :=
  let i := slot h
  if hi : i < es.size then
    let old := es[i]
    -- NOTE: Clearing the slot before the recursive call leaves the child unshared
    -- whenever the array was, so the child can be updated in place. Every arm
    -- writes into the cleared array: in this shape the compiler keeps the
    -- clearing write before the recursion, which `HAMTVerifyTests/ReleaseIR.lean` checks.
    let es' := es.set i .null
    have hi' : i < es'.size := by simpa [es'] using hi
    match he : old with
    | .null => es'.set i (.entry key) hi'
    | .entry k =>
      if key == k then es'.set i (.entry key) hi'
      else es'.set i (.ref (mkCollisionNode k key)) hi'
    | .ref child =>
      es'.set i (.ref (childInsert child (he ▸ Array.getElem_mem hi) (nextHash h) key)) hi'
  else es

/-- Logically, `insertEntries` writes one entry into the selected slot; the
clearing write only matters at runtime. -/
theorem insertEntries_eq [BEq α] (es : Array (Entry α (Node α)))
    (childInsert : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (h : USize) (key : α) (hi : slot h < es.size) :
    insertEntries es childInsert h key =
      es.set (slot h) (match es[slot h], Array.getElem_mem hi with
        | .null, _ => .entry key
        | .entry k, _ => if key == k then .entry key
            else .ref (mkCollisionNode k key)
        | .ref child, hmem => .ref (childInsert child hmem (nextHash h) key)) hi := by
  simp only [insertEntries, dif_pos hi]
  split <;> split <;> (try split) <;> simp_all

-- A special path for insertion below the depth limit
-- NOTE: The promotion limit does not bound the depth of an existing input tree.
-- This path still descends that tree, using the callback's membership proof to
-- decrease `sizeOf node`. The other callers of `insertEntries` ignore that proof:
-- `insertNode` decreases `levels`, while `rebuild` decreases the unprocessed suffix.
/-- At the depth limit, continue along existing nodes without promoting buckets. -/
def insertNoExpand [BEq α] (node : Node α) (hash : USize)
    (key : α) : Node α :=
  match node with
  | .collision keys =>
    (insertCollision keys key).val
  | .entries es =>
    .entries (insertEntries es (fun child _ => insertNoExpand child) hash key)
termination_by sizeOf node
decreasing_by
  have h := Array.sizeOf_lt_of_mem ‹_›
  simp at h ⊢
  omega

-- Corresponding to `traverse` inside `insertAux`
-- NOTE: Invariant: *insertion into an entries node always returns an entries node*, even if
-- a slot becomes a reference to a collision node. Using an array accumulator
-- encodes this invariant in the type, so the caller can wrap `.entries` once
-- around the entire rebuild. No well-formedness assumption is needed for this.
/-- Reinsert a collision node's keys in their original order, recomputing
hashes at the current offset. Specializing the child callback removes indirect
calls from the compiled rebuild loop. -/
@[specialize] def rebuild [BEq α] [Hashable α]
    (childInsert : Node α → USize → α → Node α) (offset : USize)
    (b : CollisionNode α) (i : Nat) (es : Array (Entry α (Node α))) :
    Array (Entry α (Node α)) :=
  match b with
  | ⟨.collision keys, _⟩ =>
    if hi : i < keys.size then
      let key := keys[i]
      let h := (hash key).toUSize >>> offset
      rebuild childInsert offset b (i + 1) (insertEntries es (fun child _ => childInsert child) h key)
    else es
  | ⟨.entries _, h⟩ => nomatch h
termination_by getCollisionNodeSize b - i
decreasing_by simp only [getCollisionNodeSize]; omega

-- Corresponding to `insertAux`
/-- Insertion with a cached hash and a scalar bit offset. `levels` counts the
remaining levels at which collision nodes may be promoted. Rebuilding calls
entries insertion at this level and node insertion at a strictly smaller level.
At zero promotion levels the existing tree is still fully traversed. -/
def insertNode [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (node : Node α) (h : USize) (key : α) : Node α :=
  match levels with
  | 0 => insertNoExpand node h key
  | levels + 1 =>
    match node with
    | .entries es => .entries (insertEntries es
        (fun child _ => insertNode levels (offset + shift) child) h key)
    | .collision keys =>
      let b := insertCollision keys key
      if getCollisionNodeSize b < maxCollisions then b.val
      -- NOTE: Rebuilding routes keys at the current `offset`, but its callback
      -- inserts into children with `offset + shift` and one fewer level. Calling
      -- full `insertNode` on the accumulator at the current level would not
      -- decrease `levels`; `insertEntries` performs that local step without recursion.
      else .entries (rebuild (insertNode levels (offset + shift))
        offset b 0 mkEmptyEntriesArray)

/-- Insert into the keys-only representation. As upstream, the root has depth 1
and promotion stops at depth 7. No equivalence to opaque partial constants is assumed. -/
def insert [BEq α] [Hashable α] (map : Raw α)
    (key : α) : Raw α :=
  ⟨insertNode (maxDepth.toNat - 1) 0 map.root (hash key).toUSize key⟩

end HAMTVerify.SetWithoutValArray.Raw
