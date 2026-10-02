module

public import HAMTVerify.Contains
public import HAMTVerify.Bindings
import all Lean.Data.PersistentHashMap

@[expose] public section

/-! Total insertion, including collision-bucket promotion at the native threshold. -/

namespace HAMTVerify

namespace Array

@[inline]
unsafe def modifyInBoundWithCallBackProofUnsafe (xs : Array α) (i : Nat) (f : (x : α) → x ∈ xs → α) (h_lt : i < xs.size) : Array α :=
  let v                := xs[i]'h_lt
  -- Replace a[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
  -- Note: we assume that arrays have a uniform representation irrespective
  -- of the element type, and that it is valid to store `box(0)` in any array.
  let xs'               := xs.set i (unsafeCast ()) h_lt
  let v := f v (Array.getElem_mem h_lt)
  xs'.set i v (Nat.lt_of_lt_of_eq h_lt (Array.size_set ..).symm)

-- NOTE: Native `Array.modify` gives its callback only a value, without proof
-- that it came from the array. The extra membership argument lets recursive
-- callers prove that a selected child is smaller; it is erased at runtime.
@[implemented_by modifyInBoundWithCallBackProofUnsafe]
def modifyInBoundWithCallBackProof (xs : Array α) (i : Nat) (f : (x : α) → x ∈ xs → α) (h_lt : i < xs.size) : Array α :=
  let v := xs[i]'h_lt
  xs.set i (f v (Array.getElem_mem h_lt)) h_lt

@[inline]
def modifyWithCallBackProof (xs : Array α) (i : Nat) (f : (x : α) → x ∈ xs → α) : Array α :=
  if h_lt : i < xs.size then modifyInBoundWithCallBackProof xs i f h_lt else xs

theorem size_modifyInBoundWithCallBackProof {xs : Array α} {i : Nat} {f : (x : α) → x ∈ xs → α} {h_lt : i < xs.size} :
  (modifyInBoundWithCallBackProof xs i f h_lt).size = xs.size := by
  simp only [modifyInBoundWithCallBackProof, Array.size_set]

theorem size_modifyWithCallBackProof {xs : Array α} {i : Nat} {f : (x : α) → x ∈ xs → α} :
  (modifyWithCallBackProof xs i f).size = xs.size := by
  simp only [modifyWithCallBackProof]
  split ; apply size_modifyInBoundWithCallBackProof ; rfl

end Array

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

-- Corresponding to `insertAtCollisionNodeAux`
/-- Replace the first matching binding, or append when the scan reaches the end.
Scanning the collision node directly allows its constructor to be reused. -/
def insertCollisionAux [BEq α] (b : CollisionNode α β) (i : Nat)
    (key : α) (value : β) : CollisionNode α β :=
  match b with
  | ⟨.collision keys vals hsz, _⟩ =>
    -- FIXME: Ideally, should not compare with `key.size` repetitively?
    if hi : i < keys.size then
      if key == keys[i] then
        ⟨.collision (keys.set i key) (vals.set i value (hsz ▸ hi))
          (by simp [hsz]), .mk ..⟩
      else insertCollisionAux b (i + 1) key value
    else
      ⟨.collision (keys.push key) (vals.push value) (by simp [hsz]), .mk ..⟩
  | ⟨.entries _, h⟩ => nomatch h
termination_by getCollisionNodeSize b - i
decreasing_by simp only [getCollisionNodeSize]; omega

@[inline] def insertCollision [BEq α] (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (key : α) (value : β) : CollisionNode α β :=
  insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ 0 key value

-- The `Node.entries` branch of `insertAux`
/-- Entries update with an already computed hash. The child callback receives
proof that the child is referenced by the original entries array. -/
@[inline] def insertEntries [BEq α]
    (es : Array (Entry α β (Node α β)))
    -- NOTE: `insertEntries` handles the current level; `childInsert` handles the next level.
    -- Only the `.ref` case consumes another hash chunk and invokes the callback.
    (childInsert : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (h : USize) (key : α) (value : β) :
    Array (Entry α β (Node α β)) :=
  Array.modifyWithCallBackProof es (slot h) fun
    | .null, _ => .entry key value
    | .entry k v, _ => if key == k then .entry key value
        else .ref (mkCollisionNode k v key value)
    | .ref child, hmem => .ref (childInsert child hmem (nextHash h) key value)

-- A special path for insertion below the depth limit
-- NOTE: The promotion limit does not bound the depth of an existing input tree.
-- This path still descends that tree, using the callback's membership proof to
-- decrease `sizeOf node`. The other callers of `insertEntries` ignore that proof:
-- `insertNode` decreases `levels`, while `rebuild` decreases the unprocessed suffix.
/-- At the depth limit, continue along existing nodes without promoting buckets. -/
def insertNoExpand [BEq α] (node : Node α β) (hash : USize)
    (key : α) (value : β) : Node α β :=
  match node with
  | .collision keys vals hsz =>
    (insertCollision keys vals hsz key value).val
  | .entries es =>
    .entries (insertEntries es (fun child _ => insertNoExpand child) hash key value)
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
/-- Reinsert a collision node's bindings in their original order, recomputing
hashes at the current offset. Specializing the child callback removes indirect
calls from the compiled rebuild loop. -/
@[specialize] def rebuild [BEq α] [Hashable α]
    (childInsert : Node α β → USize → α → β → Node α β) (offset : USize)
    (b : CollisionNode α β) (i : Nat) (es : Array (Entry α β (Node α β))) :
    Array (Entry α β (Node α β)) :=
  match b with
  | ⟨.collision keys vals hsz, _⟩ =>
    -- FIXME: Ideally, should not compare with `key.size` repetitively?
    if hi : i < keys.size then
      let key := keys[i]
      let h := (hash key).toUSize >>> offset
      let val := vals[i]'(hsz ▸ hi)
      rebuild childInsert offset b (i + 1) (insertEntries es (fun child _ => childInsert child) h key val)
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
    (node : Node α β) (h : USize) (key : α) (value : β) : Node α β :=
  match levels with
  | 0 => insertNoExpand node h key value
  | levels + 1 =>
    match node with
    | .entries es => .entries (insertEntries es
        (fun child _ => insertNode levels (offset + shift) child) h key value)
    | .collision keys vals hsz =>
      let b := insertCollision keys vals hsz key value
      if getCollisionNodeSize b < maxCollisions then b.val
      -- NOTE: Rebuilding routes keys at the current `offset`, but its callback
      -- inserts into children with `offset + shift` and one fewer level. Calling
      -- full `insertNode` on the accumulator at the current level would not
      -- decrease `levels`; `insertEntries` performs that local step without recursion.
      else .entries (rebuild (insertNode levels (offset + shift))
        offset b 0 mkEmptyEntriesArray)

/-- Insert into the native representation. As upstream, the root has depth 1
and promotion stops at depth 7. No equivalence to opaque partial constants is assumed. -/
def insert [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β)
    (key : α) (value : β) : Lean.PersistentHashMap α β :=
  ⟨insertNode (maxDepth.toNat - 1) 0 map.root (hash key).toUSize key value⟩

end HAMTVerify
