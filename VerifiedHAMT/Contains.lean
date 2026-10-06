module

public import VerifiedHAMT.Basic
import all Lean.Data.PersistentHashMap

@[expose] public section

/-!
A total counterpart of `Lean.PersistentHashMap.contains`, on the native node
type. The upstream `partial` definitions are opaque to the kernel; the theorems
here concern this total implementation, not an assumed equality with them.
-/

namespace VerifiedHAMT

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

/--
The native hash-directed traversal, with structural termination. The explicit
bounds check returns `false` on a malformed short entries array; on valid nodes
the selected slot is in bounds. Values are irrelevant to membership.
-/
def containsNode [BEq α] (node : Node α β) (hash : USize) (key : α) : Bool :=
  match node with
  -- NOTE: `contains` uses `Array.any`, which in turn uses `Array.anyM`,
  -- which seems optimized?
  | .collision keys _ _ => keys.contains key
  | .entries es =>
    let i := slot hash
    if hi : i < es.size then
      match he : es[i] with
      | .null => false
      | .entry key' _ => key == key'
      | .ref child => containsNode child (nextHash hash) key
    else false
termination_by sizeOf node
decreasing_by
  have h := Array.sizeOf_get es i hi
  rw [he] at h
  simp at h ⊢
  omega

-- FIXME: Should not repeat
/-- A lookup equation without the termination proof's dependent match. -/
theorem containsNode_entries [BEq α] (es : Array (Entry α β (Node α β)))
    (hash : USize) (key : α) :
    containsNode (.entries es) hash key =
      if hi : slot hash < es.size then
        match es[slot hash] with
        | .null => false
        | .entry key' _ => key == key'
        | .ref child => containsNode child (nextHash hash) key
      else false := by
  rw [containsNode]
  split
  · split <;> simp_all
  · rfl

/-- A provable replacement for `Lean.PersistentHashMap.contains`. -/
def contains [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β) (key : α) : Bool :=
  containsNode map.root (hash key).toUSize key

/-- A successful query cannot invent a key, even in a malformed node. -/
theorem containsNode_sound [BEq α] [LawfulBEq α] (node : Node α β)
    (hash : USize) (key : α) (found : containsNode node hash key = true) :
    HasKey key node := by
  cases node with
  | collision keys vals hsz =>
    rw [hasKey_collision]
    simp [containsNode] at found
    exact found
  | entries es =>
    by_cases hi : slot hash < es.size
    · rw [containsNode, dif_pos hi] at found
      split at found
      · contradiction
      · rename_i key' value he
        have heq : key = key' := by simpa using found
        subst key'
        exact HasKey.entry he
      · rename_i child he
        have hlt : sizeOf child < sizeOf es := by
          have h := Array.sizeOf_get es (slot hash) hi
          rw [he] at h
          simp at h
          omega
        apply HasKey.ref he
        exact containsNode_sound child (nextHash hash) key found
    · simp [containsNode, hi] at found
termination_by sizeOf node
decreasing_by simp_all; omega

/-- On a well-formed node, hash-directed traversal finds every stored key. -/
theorem containsNode_complete [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α)
    (member : HasKey key node) : containsNode node (hashAt key) key = true := by
  induction wf with
  | collision hashAt keys vals hsz =>
    simpa [containsNode] using (hasKey_collision.mp member)
  | @entries hashAt es size_eq routing children ih =>
    obtain ⟨i, hi, hkey⟩ := hasKey_entries.mp member
    have hslot := routing i hi key hkey
    subst i
    rw [containsNode, dif_pos hi]
    cases he : es[slot (hashAt key)] <;> simp [EntryHasKey] at * <;> grind

theorem containsNode_eq_true_iff [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α) :
    containsNode node (hashAt key) key = true ↔ HasKey key node :=
  ⟨containsNode_sound node (hashAt key) key, containsNode_complete wf key⟩

/-- `contains` is exactly structural key membership, assuming the map invariant. -/
theorem contains_eq_true_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    contains map key = true ↔ Mem key map :=
  containsNode_eq_true_iff wf key

theorem contains_eq_false_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    contains map key = false ↔ ¬ Mem key map := by
  rw [← contains_eq_true_iff map wf key]
  cases contains map key <;> simp

@[scoped simp] theorem contains_empty [BEq α] [LawfulBEq α] [Hashable α] (key : α) :
    contains (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) key = false :=
  (contains_eq_false_iff _ valid_empty key).mpr (not_mem_empty key)

end VerifiedHAMT
