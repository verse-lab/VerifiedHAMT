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

namespace HAMTVerify

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

/-- A key occurs somewhere in a node, regardless of which hash branch stores it. -/
inductive HasKey (key : α) : Node α β → Prop where
  | entry {es : Array (Entry α β (Node α β))} {i : Nat} {hi : i < es.size} {v : β}
      (atIndex : es[i] = .entry key v) : HasKey key (.entries es)
  | ref {es : Array (Entry α β (Node α β))} {i : Nat} {hi : i < es.size}
      {child : Node α β} (atIndex : es[i] = .ref child)
      (inChild : HasKey key child) : HasKey key (.entries es)
  | collision {keys : Array α} {vals : Array β} {hsz : keys.size = vals.size}
      (inKeys : key ∈ keys) : HasKey key (.collision keys vals hsz)

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

/-- Abstract membership of a key in a native map. -/
def Mem [BEq α] [Hashable α] (key : α) (map : Lean.PersistentHashMap α β) : Prop :=
  HasKey key map.root

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

end HAMTVerify
