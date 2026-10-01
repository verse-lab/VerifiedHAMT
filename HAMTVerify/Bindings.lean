import HAMTVerify.Basic

/-! Structural key/value membership and the additional invariant needed for updates. -/

namespace HAMTVerify

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

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

/-- No duplicate keys in an array, expressed through indices. -/
def DistinctKeys (keys : Array α) : Prop :=
  ∀ (i : Nat) (hi : i < keys.size) (j : Nat) (hj : j < keys.size),
    keys[i] = keys[j] → i = j

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

/-- Exact map update: bind the inserted key to its new value, retain other bindings. -/
def Updated (before after : Node α β) (key : α) (value : β) : Prop :=
  ∀ q w, HasBinding q w after ↔
    (q = key ∧ w = value) ∨ (q ≠ key ∧ HasBinding q w before)

theorem EntryHasBinding.hasKey {q : α} {w : β} {e : Entry α β (Node α β)}
    (h : EntryHasBinding q w e) : EntryHasKey q e := by
  cases e with
  | null => exact h
  | entry k v => exact h.1
  | ref child => exact HasBinding.hasKey h

theorem exists_getElem_set {γ : Type w} (p : γ → Prop) (xs : Array γ)
    (i : Nat) (hi : i < xs.size) (x : γ) :
    (∃ (j : Nat) (hj : j < (xs.set i x).size), p (xs.set i x)[j]) ↔
      p x ∨ ∃ (j : Nat) (hj : j < xs.size), j ≠ i ∧ p xs[j] := by
  constructor
  · rintro ⟨j, hj, hp⟩
    by_cases hji : j = i
    · subst j; exact Or.inl (by simpa using hp)
    · exact Or.inr ⟨j, by simpa using hj, hji, by simpa [Array.getElem_set, hji, Ne.symm hji] using hp⟩
  · rintro (hp | ⟨j, hj, hji, hp⟩)
    · exact ⟨i, by simpa using hi, by simpa using hp⟩
    · exact ⟨j, by simpa using hj, by simpa [Array.getElem_set, hji, Ne.symm hji] using hp⟩

theorem wellFormed_set {hashAt : α → USize} {es : Array (Entry α β (Node α β))}
    (wf : WellFormed hashAt (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α β (Node α β))
    (route : ∀ q, EntryHasKey q e → slot (hashAt q) = i)
    (child : ∀ n, e = .ref n → WellFormed (fun q => nextHash (hashAt q)) n) :
    WellFormed hashAt (.entries (es.set i e)) := by
  cases wf with
  | entries size_eq routing children =>
    apply WellFormed.entries (by simpa using size_eq)
    · intro j hj q hq
      by_cases hji : j = i
      · subst j; apply route q; simpa using hq
      · apply routing j (by simpa using hj) q
        simpa [Array.getElem_set, hji, Ne.symm hji] using hq
    · intro j hj n hn
      by_cases hji : j = i
      · subst j; apply child n; simpa using hn
      · apply children j (by simpa using hj) n
        simpa [Array.getElem_set, hji, Ne.symm hji] using hn

theorem unique_set {es : Array (Entry α β (Node α β))}
    (hu : Unique (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α β (Node α β)) (child : ∀ n, e = .ref n → Unique n) :
    Unique (.entries (es.set i e)) := by
  cases hu with
  | entries children =>
    apply Unique.entries
    intro j hj n hn
    by_cases hji : j = i
    · subst j; apply child n; simpa using hn
    · apply children j (by simpa using hj) n
      simpa [Array.getElem_set, hji, Ne.symm hji] using hn

theorem hasKey_set_iff {es : Array (Entry α β (Node α β))}
    (i : Nat) (hi : i < es.size) (e : Entry α β (Node α β)) (key : α)
    (mem : ∀ q, EntryHasKey q e ↔ q = key ∨ EntryHasKey q es[i]) (q : α) :
    HasKey q (.entries (es.set i e)) ↔ q = key ∨ HasKey q (.entries es) := by
  rw [hasKey_entries, exists_getElem_set, mem, hasKey_entries]
  constructor
  · rintro ((hk | he) | ⟨j, hj, _, he⟩)
    · exact Or.inl hk
    · exact Or.inr ⟨i, hi, he⟩
    · exact Or.inr ⟨j, hj, he⟩
  · rintro (hk | ⟨j, hj, he⟩)
    · exact Or.inl (Or.inl hk)
    · by_cases hji : j = i
      · subst j; exact Or.inl (Or.inr he)
      · exact Or.inr ⟨j, hj, hji, he⟩

theorem updated_set {hashAt : α → USize} {es : Array (Entry α β (Node α β))}
    (wf : WellFormed hashAt (.entries es)) (key : α) (value : β)
    (hi : slot (hashAt key) < es.size) (e : Entry α β (Node α β))
    (upd : ∀ q w, EntryHasBinding q w e ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ EntryHasBinding q w es[slot (hashAt key)])) :
    Updated (.entries es) (.entries (es.set (slot (hashAt key)) e)) key value := by
  intro q w
  rw [hasBinding_entries, exists_getElem_set, upd, hasBinding_entries]
  have route : ∀ (j : Nat) (hj : j < es.size), EntryHasBinding q w es[j] →
      slot (hashAt q) = j := by
    cases wf with | entries _ routing _ => exact fun j hj h => routing j hj q h.hasKey
  constructor
  · rintro ((hnew | ⟨hne, hold⟩) | ⟨j, hj, hji, hold⟩)
    · exact Or.inl hnew
    · exact Or.inr ⟨hne, _, hi, hold⟩
    · refine Or.inr ⟨?_, j, hj, hold⟩
      intro heq
      subst q
      exact hji (route j hj hold).symm
  · rintro (hnew | ⟨hne, j, hj, hold⟩)
    · exact Or.inl (Or.inl hnew)
    · by_cases hji : j = slot (hashAt key)
      · subst j; exact Or.inl (Or.inr ⟨hne, hold⟩)
      · exact Or.inr ⟨j, hj, hji, hold⟩

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

end HAMTVerify
