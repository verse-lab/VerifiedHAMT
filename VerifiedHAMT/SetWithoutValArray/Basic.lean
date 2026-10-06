module

public import VerifiedHAMT.Basic

@[expose] public section

/-! A keys-only HAMT, adapted from Lean.PersistentHashMap and VerifiedHAMT.Basic.
The branching factor, collision threshold, and depth limit are unchanged.
Neither a leaf nor a collision bucket stores values. -/

namespace VerifiedHAMT.SetWithoutValArray

open Lean.PersistentHashMap (branching maxCollisions)

inductive Entry (α : Type u) (σ : Type v) where
  | entry (key : α)
  | ref (node : σ)
  | null

instance : Inhabited (Entry α σ) := ⟨.null⟩

inductive Node (α : Type u) where
  | entries (es : Array (Entry α (Node α)))
  | collision (keys : Array α)

instance : Inhabited (Node α) := ⟨.entries #[]⟩

def mkEmptyEntriesArray : Array (Entry α (Node α)) :=
  Array.replicate branching.toNat .null

-- Compiled as a shared closed value; insertion does not rebuild this empty node.
def mkEmptyEntries : Node α := .entries mkEmptyEntriesArray

inductive IsCollisionNode : Node α → Prop where
  | mk (keys : Array α) : IsCollisionNode (.collision keys)

abbrev CollisionNode (α : Type u) := { n : Node α // IsCollisionNode n }

-- Keep this call boundary: inlining can sink the old keys.size read past
-- collision insertion, retaining the old array and forcing a copy (Lean 4.32).
@[noinline] def getCollisionNodeSize : CollisionNode α → Nat
  | ⟨.collision keys, _⟩ => keys.size
  | ⟨.entries _, h⟩ => nomatch h

def mkCollisionNode (k₁ k₂ : α) : Node α :=
  .collision ((Array.mkEmpty maxCollisions).push k₁ |>.push k₂)

end VerifiedHAMT.SetWithoutValArray

/-- Raw keys-only tree. The public set bundles this with its size and proofs. -/
structure VerifiedHAMT.SetWithoutValArray.Raw (α : Type u) [BEq α] [Hashable α] where
  root : SetWithoutValArray.Node α := SetWithoutValArray.mkEmptyEntries

namespace VerifiedHAMT.SetWithoutValArray.Raw

variable {α : Type u}

open Lean.PersistentHashMap (branching)

@[inline] def empty [BEq α] [Hashable α] : Raw α := {}

instance [BEq α] [Hashable α] : EmptyCollection (Raw α) := ⟨empty⟩
instance [BEq α] [Hashable α] : Inhabited (Raw α) := ⟨empty⟩

section HasKey

-- NOTE: There is `Node`, and there is `Entry`. Give each its own membership predicate.

/-- A key occurs somewhere in a node, regardless of which hash branch stores it. -/
inductive HasKey (key : α) : Node α → Prop where
  | entry {es : Array (Entry α (Node α))} {i : Nat} {hi : i < es.size}
      (atIndex : es[i] = .entry key) : HasKey key (.entries es)
  | ref {es : Array (Entry α (Node α))} {i : Nat} {hi : i < es.size}
      {child : Node α} (atIndex : es[i] = .ref child)
      (inChild : HasKey key child) : HasKey key (.entries es)
  | collision {keys : Array α}
      (inKeys : key ∈ keys) : HasKey key (.collision keys)

/-- Abstract membership, independent of the hash-directed query. -/
def Mem [BEq α] [Hashable α] (key : α) (map : VerifiedHAMT.SetWithoutValArray.Raw α) : Prop :=
  HasKey key map.root

/-- Structural key membership in one entry. -/
def EntryHasKey (key : α) : Entry α (Node α) → Prop
  | .null => False
  | .entry key' => key = key'
  | .ref child => HasKey key child

@[scoped simp] theorem hasKey_collision {keys : Array α} {key : α} :
    HasKey key (.collision keys) ↔ key ∈ keys := by
  constructor
  · intro h; cases h with | collision h => exact h
  · exact HasKey.collision

theorem hasKey_entries {es : Array (Entry α (Node α))} {key : α} :
    HasKey key (.entries es) ↔ ∃ (i : Nat) (hi : i < es.size), EntryHasKey key es[i] := by
  constructor
  · intro h
    cases h with
    | @entry _ i hi h => exact ⟨i, hi, by simp [h, EntryHasKey]⟩
    | @ref _ i hi child h hk => exact ⟨i, hi, by simpa [h, EntryHasKey] using hk⟩
  · rintro ⟨i, hi, hk⟩
    cases h : es[i] with
    | null => simp [h, EntryHasKey] at hk
    | entry key' =>
      have heq : key = key' := by simpa [h, EntryHasKey] using hk
      subst key'
      exact HasKey.entry h
    | ref child =>
      exact HasKey.ref h (by simpa [h, EntryHasKey] using hk)

theorem hasKey_set_iff {es : Array (Entry α (Node α))}
    (i : Nat) (hi : i < es.size) (e : Entry α (Node α)) (key : α)
    (mem : ∀ q, EntryHasKey q e ↔ q = key ∨ EntryHasKey q es[i]) (q : α) :
    HasKey q (.entries (es.set i e)) ↔ q = key ∨ HasKey q (.entries es) := by
  simp [hasKey_entries, Array.getElem_set]
  grind

@[scoped simp] theorem hasKey_mkCollisionNode (k₁ k₂ q : α) :
    HasKey q (mkCollisionNode k₁ k₂) ↔ q = k₁ ∨ q = k₂ := by
  simp [mkCollisionNode]

end HasKey

section WellFormed

/--
The shape and routing invariants needed for membership queries. `hashAt` is the
unconsumed hash at this node. Every entries array has the native branching size;
every stored key is in its prescribed slot; child nodes consume another chunk.

No uniqueness or collision-bucket size assumption is needed for `contains`.
This predicate does not assume any correctness property of a lookup function.
-/
inductive WellFormed : (α → USize) → Node α → Prop where
  | collision (hashAt : α → USize) (keys : Array α) : WellFormed hashAt (.collision keys)
  | entries {hashAt : α → USize} {es : Array (Entry α (Node α))}
      (size_eq : es.size = branching.toNat)
      (routing : ∀ (i : Nat) (hi : i < es.size) (key : α),
        EntryHasKey key es[i] → slot (hashAt key) = i)
      (children : ∀ (i : Nat) (hi : i < es.size) (child : Node α),
        es[i] = .ref child → WellFormed (fun key => nextHash (hashAt key)) child) :
      WellFormed hashAt (.entries es)

/-- The lookup invariant at the root of a keys-only set. -/
def Valid [BEq α] [Hashable α] (map : VerifiedHAMT.SetWithoutValArray.Raw α) : Prop :=
  WellFormed (fun key => (hash key).toUSize) map.root

theorem WellFormed.slot_lt {hashAt : α → USize}
    {es : Array (Entry α (Node α))} (wf : WellFormed hashAt (.entries es))
    (hash : USize) : slot hash < es.size := by
  cases wf with
  | entries size_eq _ _ => simpa only [size_eq] using slot_lt_branching hash

theorem wellFormed_empty (hashAt : α → USize) :
    WellFormed hashAt mkEmptyEntries := by
  apply WellFormed.entries
  · simp [mkEmptyEntriesArray]
  · intro i hi key hk
    simp [mkEmptyEntriesArray, EntryHasKey] at hk
  · intro i hi child hc
    simp [mkEmptyEntriesArray] at hc

@[scoped simp] theorem valid_empty [BEq α] [Hashable α] :
    Valid (empty : VerifiedHAMT.SetWithoutValArray.Raw α) :=
  wellFormed_empty _

@[scoped simp] theorem not_mem_empty [BEq α] [Hashable α] (key : α) :
    ¬ Mem key (empty : VerifiedHAMT.SetWithoutValArray.Raw α) := by
  simp [Mem, empty, mkEmptyEntries, hasKey_entries, mkEmptyEntriesArray, EntryHasKey]

theorem wellFormed_mkCollisionNode (hashAt : α → USize) (k₁ k₂ : α) :
    WellFormed hashAt (mkCollisionNode k₁ k₂) := .collision _ _

theorem wellFormed_collisionNode (hashAt : α → USize) (b : CollisionNode α) :
    WellFormed hashAt b.val := by
  obtain ⟨node, hb⟩ := b
  cases hb
  exact .collision _ _

end WellFormed

theorem wellFormed_set {hashAt : α → USize} {es : Array (Entry α (Node α))}
    (wf : WellFormed hashAt (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α (Node α))
    (route : ∀ q, EntryHasKey q e → slot (hashAt q) = i)
    (child : ∀ n, e = .ref n → WellFormed (fun q => nextHash (hashAt q)) n) :
    WellFormed hashAt (.entries (es.set i e)) := by
  cases wf with
  | entries size_eq routing children =>
    apply WellFormed.entries (by simpa using size_eq) <;> grind


section Uniqueness

/-- No duplicate keys in an array, expressed through indices. -/
def DistinctKeys (keys : Array α) : Prop :=
  ∀ (i : Nat) (hi : i < keys.size) (j : Nat) (hj : j < keys.size),
    keys[i] = keys[j] → i = j

theorem DistinctKeys.push {keys : Array α} (hu : DistinctKeys keys)
    {key : α} (fresh : key ∉ keys) : DistinctKeys (keys.push key) := by
  intro i hi j hj he ; simp [DistinctKeys] at hu ; grind

/-- With `WellFormed`, this excludes duplicate keys anywhere in the tree.
Routing already separates keys in different entries slots. -/
inductive Unique : Node α → Prop where
  | collision {keys : Array α}
      (distinct : DistinctKeys keys) : Unique (.collision keys)
  | entries {es : Array (Entry α (Node α))}
      (children : ∀ (i : Nat) (hi : i < es.size) (child : Node α),
        es[i] = .ref child → Unique child) : Unique (.entries es)

theorem unique_empty : Unique (mkEmptyEntries : Node α) := by
  apply Unique.entries
  intro i hi child hc
  simp [mkEmptyEntriesArray] at hc

theorem unique_mkCollisionNode {k₁ k₂ : α} (hne : k₁ ≠ k₂) :
    Unique (mkCollisionNode k₁ k₂) := by
  apply Unique.collision
  intro i hi j hj
  have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
  have hj' : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> simp_all [Ne.symm hne]

theorem unique_set {es : Array (Entry α (Node α))}
    (hu : Unique (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α (Node α)) (child : ∀ n, e = .ref n → Unique n) :
    Unique (.entries (es.set i e)) := by
  cases hu with
  | entries children => apply Unique.entries <;> grind


end Uniqueness

end VerifiedHAMT.SetWithoutValArray.Raw
