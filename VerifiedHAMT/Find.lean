module

public import VerifiedHAMT.Contains
public import VerifiedHAMT.InsertProofs
import all Lean.Data.PersistentHashMap

@[expose] public section

/-! Total value lookup on the native HAMT. Specifications use structural bindings,
not the opaque upstream `partial` lookup. Values require no typeclass instances. -/

namespace VerifiedHAMT

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

/-- Search a collision suffix, returning the first matching value. -/
def findCollisionAux [BEq α] (keys : Array α) (vals : Array β)
    (hsz : keys.size = vals.size) (i : Nat) (key : α) : Option β :=
  if hi : i < keys.size then
    if key == keys[i] then some (vals[i]'(hsz ▸ hi))
    else findCollisionAux keys vals hsz (i + 1) key
  else none
termination_by keys.size - i

-- NOTE: Keep `@&`: on Lean v4.32.0, automatic borrow inference alone leaves
-- extra node/array reference counting in the Nat specialization. The annotation
-- enables borrowed traversal without affecting the logical definition or proofs.
/-- Hash-directed traversal with structural termination. Short malformed entries
arrays return `none`; collision value indices are justified by equal array sizes. -/
def findNode [BEq α] (node : @& Node α β) (hash : USize) (key : α) : Option β :=
  match node with
  | .collision keys vals hsz => findCollisionAux keys vals hsz 0 key
  | .entries es =>
    if hi : slot hash < es.size then
      match he : es[slot hash] with
      | .null => none
      | .entry key' value => if key == key' then some value else none
      | .ref child => findNode child (nextHash hash) key
    else none
termination_by sizeOf node
decreasing_by
  have h := Array.sizeOf_get es (slot hash) hi
  rw [he] at h
  simp at h ⊢
  omega

-- FIXME: Should not repeat
theorem findNode_entries [BEq α] (es : Array (Entry α β (Node α β)))
    (hash : USize) (key : α) :
    findNode (.entries es) hash key =
      if hi : slot hash < es.size then
        match es[slot hash] with
        | .null => none
        | .entry key' value => if key == key' then some value else none
        | .ref child => findNode child (nextHash hash) key
      else none := by
  rw [findNode]
  split
  · split <;> simp_all
  · rfl

-- NOTE: `@&` makes the generic API borrow the map.
-- Although the `Nat` specialization still infers this borrow even without the map annotation
-- when `findNode` is annotated, this is not the general case.
/-- Total counterpart of `Lean.PersistentHashMap.find?`. -/
def find? [BEq α] [Hashable α] (map : @& Lean.PersistentHashMap α β) (key : α) : Option β :=
  findNode map.root (hash key).toUSize key

/-- Use the supplied default when lookup misses. -/
@[inline] def findD [BEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (key : α) (fallback : β) : β :=
  (find? map key).getD fallback

section Soundness

theorem findCollisionAux_sound [BEq α] [LawfulBEq α]
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (i : Nat) (key : α) (value : β)
    (found : findCollisionAux keys vals hsz i key = some value) :
    ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = key ∧
      vals[j]'(hsz ▸ hj) = value := by
  rw [findCollisionAux] at found
  split at found
  · rename_i hi
    split at found
    · grind
    · obtain ⟨j, hj, hij, hk, hv⟩ :=
        findCollisionAux_sound keys vals hsz (i + 1) key value found
      exact ⟨j, hj, by omega, hk, hv⟩
  · contradiction
termination_by keys.size - i

/-- Successful lookup returns a stored binding even without routing or uniqueness. -/
theorem findNode_sound [BEq α] [LawfulBEq α] (node : Node α β)
    (hash : USize) (key : α) (value : β) (found : findNode node hash key = some value) :
    HasBinding key value node := by
  cases node with
  | collision keys vals hsz =>
    rw [findNode] at found
    obtain ⟨i, hi, _, hk, hv⟩ :=
      findCollisionAux_sound keys vals hsz 0 key value found
    exact .collision hi hk hv
  | entries es =>
    rw [findNode_entries] at found
    split at found
    · rename_i hi
      split at found
      · contradiction
      · rename_i key' val he
        split at found
        · rename_i hk
          have heq : key = key' := eq_of_beq hk
          have hv : val = value := Option.some.inj found
          subst key'; subst val
          exact .entry he
        · contradiction
      · rename_i child he
        have hlt : sizeOf child < sizeOf es := by
          have h := Array.sizeOf_get es (slot hash) hi
          rw [he] at h
          simp at h
          omega
        exact .ref he (findNode_sound child (nextHash hash) key value found)
    · contradiction
termination_by sizeOf node
decreasing_by simp_all; omega

end Soundness

section Completeness

theorem findCollisionAux_eq_none_iff [BEq α] [LawfulBEq α]
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (i : Nat) (key : α) :
    findCollisionAux keys vals hsz i key = none ↔
      ∀ (j : Nat) (hj : j < keys.size), i ≤ j → keys[j] ≠ key := by
  rw [findCollisionAux]
  split
  · rename_i hi
    split
    · grind
    · rw [findCollisionAux_eq_none_iff keys vals hsz (i + 1) key]
      grind
  · grind
termination_by keys.size - i

/-- Every stored key has a lookup result under routing alone. Duplicate keys may
have several bindings, but the algorithm still returns one of them. -/
theorem findNode_exists_of_hasKey [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α)
    (member : HasKey key node) : ∃ value, findNode node (hashAt key) key = some value := by
  induction wf with
  | collision hashAt keys vals hsz =>
    have hk := hasKey_collision.mp member
    have hn : findCollisionAux keys vals hsz 0 key ≠ none := by
      intro hn
      have hall := (findCollisionAux_eq_none_iff keys vals hsz 0 key).mp hn
      obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hk
      exact hall i hi (Nat.zero_le _) he
    cases he : findCollisionAux keys vals hsz 0 key with
    | none => exact False.elim (hn he)
    | some value => exact ⟨value, by simpa only [findNode] using he⟩
  | @entries hashAt es hs routing children ih =>
    obtain ⟨i, hi, hk⟩ := hasKey_entries.mp member
    have hslot := routing i hi key hk
    subst i
    rw [findNode_entries, dif_pos hi]
    cases he : es[slot (hashAt key)] with
    | null => simp [he, EntryHasKey] at hk
    | entry key' value =>
      have heq : key = key' := by simpa [he, EntryHasKey] using hk
      exact ⟨value, by simp [heq]⟩
    | ref child =>
      exact ih _ hi child he (by simpa [he, EntryHasKey] using hk)

end Completeness

section MainParts

theorem findNode_eq_some_iff [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (hu : Unique node)
    (key : α) (value : β) :
    findNode node (hashAt key) key = some value ↔ HasBinding key value node := by
  constructor
  · exact findNode_sound node (hashAt key) key value
  · intro hb
    obtain ⟨actual, ha⟩ := findNode_exists_of_hasKey wf key hb.hasKey
    have he := HasBinding.functional wf hu (findNode_sound _ _ _ _ ha) hb
    simpa [he] using ha

theorem findNode_eq_none_iff [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α) :
    findNode node (hashAt key) key = none ↔ ¬ HasKey key node := by
  constructor
  · intro hn hk
    obtain ⟨v, hv⟩ := findNode_exists_of_hasKey wf key hk
    rw [hn] at hv
    contradiction
  · intro hk
    cases he : findNode node (hashAt key) key with
    | none => rfl
    | some value => exact False.elim (hk (findNode_sound _ _ _ _ he).hasKey)

theorem find?_eq_some_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) : find? map key = some value ↔ MapsTo key value map :=
  findNode_eq_some_iff wf hu key value

theorem find?_eq_none_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    find? map key = none ↔ ¬ Mem key map := findNode_eq_none_iff wf key

end MainParts

section DerivedParts

theorem find?_isSome_eq_contains [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    (find? map key).isSome = contains map key := by
  cases he : find? map key with
  | none =>
    have hm := (find?_eq_none_iff map wf key).mp he
    simp [(contains_eq_false_iff map wf key).mpr hm]
  | some value =>
    have hm := (findNode_sound _ _ _ _ he).hasKey
    simp [(contains_eq_true_iff map wf key).mpr hm]

@[scoped simp] theorem find?_empty [BEq α] [LawfulBEq α] [Hashable α] (key : α) :
    find? (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) key = none :=
  (find?_eq_none_iff _ valid_empty key).mpr (not_mem_empty key)

@[scoped simp] theorem find?_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value : β) :
    find? (insert map key value) q = if q == key then some value else find? map q := by
  apply Option.ext
  intro w
  rw [find?_eq_some_iff _ (valid_insert map wf key value) (unique_insert map wf hu key value),
    mapsTo_insert_iff map wf hu key q value w]
  by_cases h : q = key
  · simp [h, eq_comm]
  · simp [h, find?_eq_some_iff map wf hu q w]

@[scoped simp] theorem find?_insert_self [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) : find? (insert map key value) key = some value := by
  rw [find?_insert map wf hu]
  simp

theorem find?_insert_of_ne [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value : β) (hne : q ≠ key) :
    find? (insert map key value) q = find? map q := by
  rw [find?_insert map wf hu]
  simp [hne]

theorem findD_eq_of_mapsTo [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value fallback : β) (hb : MapsTo key value map) :
    findD map key fallback = value := by
  simp only [findD, (find?_eq_some_iff map wf hu key value).mpr hb, Option.getD_some]

theorem findD_eq_of_not_mem [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map)
    (key : α) (fallback : β) (hm : ¬ Mem key map) :
    findD map key fallback = fallback := by
  simp only [findD, (find?_eq_none_iff map wf key).mpr hm, Option.getD_none]

@[scoped simp] theorem findD_empty [BEq α] [LawfulBEq α] [Hashable α]
    (key : α) (fallback : β) :
    findD (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) key fallback = fallback := by
  simp [findD]

@[scoped simp] theorem findD_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value fallback : β) :
    findD (insert map key value) q fallback =
      if q == key then value else findD map q fallback := by
  simp only [findD, find?_insert map wf hu]
  split <;> rfl

@[scoped simp] theorem findD_insert_self [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value fallback : β) : findD (insert map key value) key fallback = value := by
  rw [findD_insert map wf hu]
  simp

end DerivedParts

end VerifiedHAMT
