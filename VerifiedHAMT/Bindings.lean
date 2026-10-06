module

public import VerifiedHAMT.Basic
import all Lean.Data.PersistentHashMap

@[expose] public section

/-! Structural key/value membership and the additional invariant needed for updates. -/

namespace VerifiedHAMT

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

/-- Exact map update: bind the inserted key to its new value, retain other bindings. -/
def Updated (before after : Node α β) (key : α) (value : β) : Prop :=
  ∀ q w, HasBinding q w after ↔
    (q = key ∧ w = value) ∨ (q ≠ key ∧ HasBinding q w before)

theorem wellFormed_set {hashAt : α → USize} {es : Array (Entry α β (Node α β))}
    (wf : WellFormed hashAt (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α β (Node α β))
    (route : ∀ q, EntryHasKey q e → slot (hashAt q) = i)
    (child : ∀ n, e = .ref n → WellFormed (fun q => nextHash (hashAt q)) n) :
    WellFormed hashAt (.entries (es.set i e)) := by
  cases wf with
  | entries size_eq routing children =>
    apply WellFormed.entries (by simpa using size_eq) <;> grind

theorem unique_set {es : Array (Entry α β (Node α β))}
    (hu : Unique (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α β (Node α β)) (child : ∀ n, e = .ref n → Unique n) :
    Unique (.entries (es.set i e)) := by
  cases hu with
  | entries children => apply Unique.entries <;> grind

theorem updated_set {hashAt : α → USize} {es : Array (Entry α β (Node α β))}
    (wf : WellFormed hashAt (.entries es)) (key : α) (value : β)
    (hi : slot (hashAt key) < es.size) (e : Entry α β (Node α β))
    (upd : ∀ q w, EntryHasBinding q w e ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ EntryHasBinding q w es[slot (hashAt key)])) :
    Updated (.entries es) (.entries (es.set (slot (hashAt key)) e)) key value := by
  intro q w
  simp [hasBinding_entries, Array.getElem_set, hasBinding_entries]
  have route : ∀ (j : Nat) (hj : j < es.size), EntryHasBinding q w es[j] →
      slot (hashAt q) = j := by
    cases wf with | entries _ routing _ => exact fun j hj h => routing j hj q h.hasKey
  constructor <;> grind

end VerifiedHAMT
