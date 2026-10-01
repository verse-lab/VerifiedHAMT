import HAMTVerify.Contains
import HAMTVerify.Bindings

/-! Total insertion, including collision-bucket promotion at the native threshold. -/

namespace HAMTVerify

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

/-- The parallel arrays of a native collision node. -/
structure Bucket (α : Type u) (β : Type v) where
  keys : Array α
  vals : Array β
  size_eq : keys.size = vals.size

def Bucket.node (b : Bucket α β) : Node α β := .collision b.keys b.vals b.size_eq

/-- Replace the first matching binding, or append when the scan reaches the end. -/
def insertAt [BEq α] (b : Bucket α β) (i : Nat) (key : α) (value : β) : Bucket α β :=
  if hi : i < b.keys.size then
    if key == b.keys[i] then
      ⟨b.keys.set i key, b.vals.set i value (b.size_eq ▸ hi), by simp [b.size_eq]⟩
    else insertAt b (i + 1) key value
  else
    ⟨b.keys.push key, b.vals.push value, by simp [b.size_eq]⟩
termination_by b.keys.size - i

/-- One entries-array update, parameterized by insertion into a child. -/
@[inline] def insertEntries [BEq α]
    (childInsert : Node α β → α → β → Node α β) (hashAt : α → USize)
    (es : Array (Entry α β (Node α β))) (key : α) (value : β) :
    Array (Entry α β (Node α β)) :=
  let i := slot (hashAt key)
  if hi : i < es.size then
    let entry := match es[i] with
      | .null => .entry key value
      | .entry k v => if key == k then .entry key value
          else .ref (mkCollisionNode k v key value)
      | .ref child => .ref (childInsert child key value)
    es.set i entry
  else es

/-- At the depth limit, continue along existing nodes without promoting buckets. -/
def insertNoExpand [BEq α] (node : Node α β) (hash : USize)
    (key : α) (value : β) : Node α β :=
  match node with
  | .collision keys vals hsz => (insertAt ⟨keys, vals, hsz⟩ 0 key value).node
  | .entries es =>
    let i := slot hash
    if hi : i < es.size then
      let entry := match he : es[i] with
        | .null => .entry key value
        | .entry k v => if key == k then .entry key value
            else .ref (mkCollisionNode k v key value)
        | .ref child => .ref (insertNoExpand child (nextHash hash) key value)
      .entries (es.set i entry)
    else .entries es
termination_by sizeOf node
decreasing_by
  have h := Array.sizeOf_get es i hi
  rw [he] at h
  simp at h ⊢
  omega

/-- Reinsert a bucket in its original order into a fresh entries array. -/
def rebuild [BEq α] (childInsert : Node α β → α → β → Node α β)
    (hashAt : α → USize) (b : Bucket α β) (i : Nat)
    (es : Array (Entry α β (Node α β))) : Array (Entry α β (Node α β)) :=
  if hi : i < b.keys.size then
    rebuild childInsert hashAt b (i + 1)
      (insertEntries childInsert hashAt es b.keys[i] (b.vals[i]'(b.size_eq ▸ hi)))
  else es
termination_by b.keys.size - i

/-- `levels` counts the remaining levels at which buckets may be promoted.
The hash function tracks the unconsumed bits and is shifted when descending.
Rebuilding calls only entries insertion at this level, and node insertion at a
strictly smaller level, so no unproved fuel exhaustion case is needed. -/
def insertNode [BEq α] (levels : Nat) (hashAt : α → USize)
    (node : Node α β) (key : α) (value : β) : Node α β :=
  match levels with
  | 0 => insertNoExpand node (hashAt key) key value
  | levels + 1 =>
    let childInsert := insertNode levels (fun k => nextHash (hashAt k))
    match node with
    | .entries es => .entries (insertEntries childInsert hashAt es key value)
    | .collision keys vals hsz =>
      let b := insertAt ⟨keys, vals, hsz⟩ 0 key value
      if b.keys.size < maxCollisions then b.node
      else .entries (rebuild childInsert hashAt b 0 mkEmptyEntriesArray)

/-- Insert into the native representation. As upstream, the root has depth 1
and promotion stops at depth 7. No equivalence to opaque partial constants is assumed. -/
def insert [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β)
    (key : α) (value : β) : Lean.PersistentHashMap α β :=
  ⟨insertNode (maxDepth.toNat - 1) (fun k => (hash k).toUSize) map.root key value⟩

end HAMTVerify
