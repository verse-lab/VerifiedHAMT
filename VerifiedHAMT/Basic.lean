module

public import Lean.Data.PersistentHashMap
public import Std
import all Lean.Data.PersistentHashMap

@[expose] public section

/-!
Structural specifications for Lean's existing persistent hash map representation.
The membership relation below inspects stored keys, independently of hashing or
any lookup algorithm.
-/

namespace VerifiedHAMT

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

section HasKey

-- NOTE: There is `Node`, and there is `Entry`. Give each its own membership predicate.

/-- A key occurs somewhere in a node, regardless of which hash branch stores it. -/
inductive HasKey (key : α) : Node α β → Prop where
  | entry {es : Array (Entry α β (Node α β))} {i : Nat} {hi : i < es.size} {v : β}
      (atIndex : es[i] = .entry key v) : HasKey key (.entries es)
  | ref {es : Array (Entry α β (Node α β))} {i : Nat} {hi : i < es.size}
      {child : Node α β} (atIndex : es[i] = .ref child)
      (inChild : HasKey key child) : HasKey key (.entries es)
  | collision {keys : Array α} {vals : Array β} {hsz : keys.size = vals.size}
      (inKeys : key ∈ keys) : HasKey key (.collision keys vals hsz)

/-- Abstract membership of a key in a native map. -/
def Mem [BEq α] [Hashable α] (key : α) (map : Lean.PersistentHashMap α β) : Prop :=
  HasKey key map.root

/-- Structural key membership in one entry. -/
def EntryHasKey (key : α) : Entry α β (Node α β) → Prop
  | .null => False
  | .entry key' _ => key = key'
  | .ref child => HasKey key child

@[scoped simp] theorem hasKey_collision {keys : Array α} {vals : Array β}
    {hsz : keys.size = vals.size} {key : α} :
    HasKey key (.collision keys vals hsz) ↔ key ∈ keys := by
  constructor
  · intro h; cases h with | collision h => exact h
  · exact HasKey.collision

theorem hasKey_entries {es : Array (Entry α β (Node α β))} {key : α} :
    HasKey key (.entries es) ↔ ∃ (i : Nat) (hi : i < es.size), EntryHasKey key es[i] := by
  constructor
  · intro h
    cases h with
    | @entry _ i hi v h => exact ⟨i, hi, by simp [h, EntryHasKey]⟩
    | @ref _ i hi child h hk => exact ⟨i, hi, by simpa [h, EntryHasKey] using hk⟩
  · rintro ⟨i, hi, hk⟩
    cases h : es[i] with
    | null => simp [h, EntryHasKey] at hk
    | entry key' v =>
      have heq : key = key' := by simpa [h, EntryHasKey] using hk
      subst key'
      exact HasKey.entry h
    | ref child =>
      exact HasKey.ref h (by simpa [h, EntryHasKey] using hk)

theorem hasKey_set_iff {es : Array (Entry α β (Node α β))}
    (i : Nat) (hi : i < es.size) (e : Entry α β (Node α β)) (key : α)
    (mem : ∀ q, EntryHasKey q e ↔ q = key ∨ EntryHasKey q es[i]) (q : α) :
    HasKey q (.entries (es.set i e)) ↔ q = key ∨ HasKey q (.entries es) := by
  simp [hasKey_entries, Array.getElem_set]
  grind

@[scoped simp] theorem hasKey_mkCollisionNode (k₁ k₂ q : α) (v₁ v₂ : β) :
    HasKey q (mkCollisionNode k₁ v₁ k₂ v₂) ↔ q = k₁ ∨ q = k₂ := by
  simp [mkCollisionNode]

end HasKey

/-- The slot and remaining hash use exactly Lean's native bit operations. -/
-- Expose the bit operations to downstream compilation instead of calling helpers.
@[inline] def slot (hash : USize) : Nat := (mod2Shift hash shift).toNat

@[inline] def nextHash (hash : USize) : USize := div2Shift hash shift

@[scoped simp] theorem slot_zero : slot 0 = 0 := by
  change ((0 : USize) &&& ((1 : USize) <<< shift - 1)).toNat = 0
  simp

/-- Every five-bit slot is in bounds for a native entries array. -/
theorem slot_lt_branching (hash : USize) : slot hash < branching.toNat := by
  have h : hash.toNat &&& 31 ≤ 31 := Nat.and_le_right
  unfold slot mod2Shift
  change (hash &&& ((1 : USize) <<< 5 - 1)).toNat < branching.toNat
  rw [USize.toNat_and]
  rcases System.Platform.numBits_eq with hb | hb <;>
    simpa [branching, shift, USize.toNat_sub, USize.toNat_shiftLeft, hb] using
      Nat.lt_succ_of_le h

section WellFormed

/--
The shape and routing invariants needed for membership queries. `hashAt` is the
unconsumed hash at this node. Every entries array has the native branching size;
every stored key is in its prescribed slot; child nodes consume another chunk.

No uniqueness or collision-bucket size assumption is needed for `contains`.
This predicate does not assume any correctness property of a lookup function.
-/
inductive WellFormed : (α → USize) → Node α β → Prop where
  | collision (hashAt : α → USize) (keys : Array α) (vals : Array β)
      (hsz : keys.size = vals.size) : WellFormed hashAt (.collision keys vals hsz)
  | entries {hashAt : α → USize} {es : Array (Entry α β (Node α β))}
      (size_eq : es.size = branching.toNat)
      (routing : ∀ (i : Nat) (hi : i < es.size) (key : α),
        EntryHasKey key es[i] → slot (hashAt key) = i)
      (children : ∀ (i : Nat) (hi : i < es.size) (child : Node α β),
        es[i] = .ref child → WellFormed (fun key => nextHash (hashAt key)) child) :
      WellFormed hashAt (.entries es)

/-- The lookup invariant at the root of a native `PersistentHashMap`. -/
def Valid [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β) : Prop :=
  WellFormed (fun key => (hash key).toUSize) map.root

theorem WellFormed.slot_lt {hashAt : α → USize}
    {es : Array (Entry α β (Node α β))} (wf : WellFormed hashAt (.entries es))
    (hash : USize) : slot hash < es.size := by
  cases wf with
  | entries size_eq _ _ => simpa only [size_eq] using slot_lt_branching hash

theorem wellFormed_empty (hashAt : α → USize) :
    WellFormed (β := β) hashAt mkEmptyEntries := by
  apply WellFormed.entries
  · simp [mkEmptyEntriesArray]
  · intro i hi key hk
    simp [mkEmptyEntriesArray, EntryHasKey] at hk
  · intro i hi child hc
    simp [mkEmptyEntriesArray] at hc

@[scoped simp] theorem valid_empty [BEq α] [Hashable α] :
    Valid (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) :=
  wellFormed_empty _

@[scoped simp] theorem not_mem_empty [BEq α] [Hashable α] (key : α) :
    ¬ Mem key (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) := by
  simp [Mem, Lean.PersistentHashMap.empty, hasKey_entries, mkEmptyEntriesArray, EntryHasKey]

theorem wellFormed_mkCollisionNode (hashAt : α → USize) (k₁ k₂ : α) (v₁ v₂ : β) :
    WellFormed hashAt (mkCollisionNode k₁ v₁ k₂ v₂) := .collision _ _ _ _

theorem wellFormed_collisionNode (hashAt : α → USize) (b : CollisionNode α β) :
    WellFormed hashAt b.val := by
  obtain ⟨node, hb⟩ := b
  cases hb
  exact .collision _ _ _ _

end WellFormed

section HasBinding

/-- A stored key/value pair, independent of any lookup algorithm. -/
inductive HasBinding (key : α) (value : β) : Node α β → Prop where
  | entry {es : Array (Entry α β (Node α β))} {i : Nat} {hi : i < es.size}
      (atIndex : es[i] = .entry key value) : HasBinding key value (.entries es)
  | ref {es : Array (Entry α β (Node α β))} {i : Nat} {hi : i < es.size}
      {child : Node α β} (atIndex : es[i] = .ref child)
      (inChild : HasBinding key value child) : HasBinding key value (.entries es)
  | collision {keys : Array α} {vals : Array β} {hsz : keys.size = vals.size}
      {i : Nat} (hi : i < keys.size) (hk : keys[i] = key)
      (hv : vals[i]'(hsz ▸ hi) = value) : HasBinding key value (.collision keys vals hsz)

def EntryHasBinding (key : α) (value : β) : Entry α β (Node α β) → Prop
  | .null => False
  | .entry k v => key = k ∧ value = v
  | .ref child => HasBinding key value child

@[scoped simp] theorem hasBinding_collision {keys : Array α} {vals : Array β}
    {hsz : keys.size = vals.size} {key : α} {value : β} :
    HasBinding key value (.collision keys vals hsz) ↔
      ∃ (i : Nat) (hi : i < keys.size), keys[i] = key ∧ vals[i]'(hsz ▸ hi) = value := by
  constructor
  · intro h; cases h with | collision hi hk hv => exact ⟨_, hi, hk, hv⟩
  · rintro ⟨i, hi, hk, hv⟩; exact .collision hi hk hv

theorem hasBinding_entries {es : Array (Entry α β (Node α β))} {key : α} {value : β} :
    HasBinding key value (.entries es) ↔
      ∃ (i : Nat) (hi : i < es.size), EntryHasBinding key value es[i] := by
  constructor
  · intro h
    cases h with
    | @entry _ i hi h => exact ⟨i, hi, by simp [h, EntryHasBinding]⟩
    | @ref _ i hi child h hb => exact ⟨i, hi, by simpa [h, EntryHasBinding] using hb⟩
  · rintro ⟨i, hi, hb⟩
    cases h : es[i] with
    | null => simp [h, EntryHasBinding] at hb
    | entry k v =>
      obtain ⟨rfl, rfl⟩ := (show key = k ∧ value = v by simpa [h, EntryHasBinding] using hb)
      exact .entry h
    | ref child => exact .ref h (by simpa [h, EntryHasBinding] using hb)

theorem HasBinding.hasKey {key : α} {value : β} {node : Node α β}
    (hb : HasBinding key value node) : HasKey key node := by
  induction hb with
  | entry h => exact .entry h
  | ref h _ ih => exact .ref h ih
  | collision hi hk _ => exact .collision (Array.mem_iff_getElem.mpr ⟨_, hi, hk⟩)

theorem EntryHasBinding.hasKey {q : α} {w : β} {e : Entry α β (Node α β)}
    (h : EntryHasBinding q w e) : EntryHasKey q e := by
  cases e with
  | null => exact h
  | entry k v => exact h.1
  | ref child => exact HasBinding.hasKey h

theorem hasKey_iff_exists_binding {key : α} {node : Node α β} :
    HasKey key node ↔ ∃ value, HasBinding key value node := by
  constructor
  · intro h
    induction h with
    | @entry es i hi value he => exact ⟨value, .entry he⟩
    | ref he _ ih => obtain ⟨v, hv⟩ := ih; exact ⟨v, .ref he hv⟩
    | @collision keys vals hsz hk =>
      obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hk
      exact ⟨vals[i]'(hsz ▸ hi), .collision hi he rfl⟩
  · rintro ⟨v, h⟩; exact h.hasKey

@[scoped simp] theorem hasBinding_mkCollisionNode (k₁ k₂ q : α) (v₁ v₂ w : β) :
    HasBinding q w (mkCollisionNode k₁ v₁ k₂ v₂) ↔
      (q = k₁ ∧ w = v₁) ∨ (q = k₂ ∧ w = v₂) := by
  simp only [mkCollisionNode, hasBinding_collision, Array.size_push, Array.mkEmpty, Array.size_empty]
  constructor
  · grind
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exists 0 ; grind
    · exists 1 ; grind

theorem collision_push_binding (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size) (key q : α) (value w : β) :
    HasBinding q w (.collision (keys.push key) (vals.push value) (by simp [hsz])) ↔
      (q = key ∧ w = value) ∨ HasBinding q w (.collision keys vals hsz) := by
  simp only [hasBinding_collision, Array.size_push, Array.getElem_push]
  constructor
  · grind
  · rintro (⟨rfl, rfl⟩ | ⟨i, hi, hk, hv⟩)
    · exists keys.size ; grind
    · grind

end HasBinding

/-- Abstract map binding, defined by the stored keys and values rather than lookup. -/
def MapsTo [BEq α] [Hashable α] (key : α) (value : β)
    (map : Lean.PersistentHashMap α β) : Prop := HasBinding key value map.root

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
inductive Unique : Node α β → Prop where
  | collision {keys : Array α} {vals : Array β} {hsz : keys.size = vals.size}
      (distinct : DistinctKeys keys) : Unique (.collision keys vals hsz)
  | entries {es : Array (Entry α β (Node α β))}
      (children : ∀ (i : Nat) (hi : i < es.size) (child : Node α β),
        es[i] = .ref child → Unique child) : Unique (.entries es)

theorem unique_empty : Unique (mkEmptyEntries : Node α β) := by
  apply Unique.entries
  intro i hi child hc
  simp [mkEmptyEntriesArray] at hc

/-- Routing and uniqueness make structural bindings single-valued. -/
theorem HasBinding.functional {hashAt : α → USize} {node : Node α β}
    (wf : WellFormed hashAt node) (hu : Unique node) {key : α} {v w : β}
    (hv : HasBinding key v node) (hw : HasBinding key w node) : v = w := by
  induction wf generalizing v w with
  | collision hashAt keys vals hsz =>
    obtain ⟨i, hi, hki, hvi⟩ := hasBinding_collision.mp hv
    obtain ⟨j, hj, hkj, hwj⟩ := hasBinding_collision.mp hw
    have hij : i = j := by
      cases hu with | collision distinct => exact distinct i hi j hj (hki.trans hkj.symm)
    subst j
    exact hvi.symm.trans hwj
  | @entries hashAt es hs route children ih =>
    obtain ⟨i, hi, hvi⟩ := hasBinding_entries.mp hv
    obtain ⟨j, hj, hwj⟩ := hasBinding_entries.mp hw
    have hij : i = j := (route i hi key hvi.hasKey).symm.trans (route j hj key hwj.hasKey)
    subst j
    cases he : es[i] with
    | null => simp [he, EntryHasBinding] at hvi
    | entry k value =>
      have h1 : v = value := (show key = k ∧ v = value by simpa [he, EntryHasBinding] using hvi).2
      have h2 : w = value := (show key = k ∧ w = value by simpa [he, EntryHasBinding] using hwj).2
      exact h1.trans h2.symm
    | ref child =>
      have hc : Unique child := by cases hu with | entries hc => exact hc i hi child he
      exact ih i hi child he hc (by simpa [he, EntryHasBinding] using hvi)
        (by simpa [he, EntryHasBinding] using hwj)

theorem unique_mkCollisionNode {k₁ k₂ : α} (hne : k₁ ≠ k₂) (v₁ v₂ : β) :
    Unique (mkCollisionNode k₁ v₁ k₂ v₂) := by
  apply Unique.collision
  intro i hi j hj
  have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
  have hj' : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> simp_all [Ne.symm hne]

end Uniqueness

end VerifiedHAMT
