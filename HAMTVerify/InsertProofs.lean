import HAMTVerify.InsertCachedProofs

namespace HAMTVerify

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

@[scoped simp] theorem hasKey_mkCollisionNode (k₁ k₂ q : α) (v₁ v₂ : β) :
    HasKey q (mkCollisionNode k₁ v₁ k₂ v₂) ↔ q = k₁ ∨ q = k₂ := by
  simp [mkCollisionNode]

@[scoped simp] theorem hasBinding_mkCollisionNode (k₁ k₂ q : α) (v₁ v₂ w : β) :
    HasBinding q w (mkCollisionNode k₁ v₁ k₂ v₂) ↔
      (q = k₁ ∧ w = v₁) ∨ (q = k₂ ∧ w = v₂) := by
  simp only [mkCollisionNode, hasBinding_collision, Array.size_push, Array.mkEmpty, Array.size_empty]
  constructor
  · rintro ⟨i, hi, hk, hv⟩
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp_all [eq_comm]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨0, by decide, by simp, by simp⟩
    · exact ⟨1, by decide, by simp, by simp⟩

theorem wellFormed_mkCollisionNode (hashAt : α → USize) (k₁ k₂ : α) (v₁ v₂ : β) :
    WellFormed hashAt (mkCollisionNode k₁ v₁ k₂ v₂) := .collision _ _ _ _

theorem unique_mkCollisionNode {k₁ k₂ : α} (hne : k₁ ≠ k₂) (v₁ v₂ : β) :
    Unique (mkCollisionNode k₁ v₁ k₂ v₂) := by
  apply Unique.collision
  intro i hi j hj he
  have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
  have hj' : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> simp_all [Ne.symm hne]

theorem insertAt_mem [BEq α] [LawfulBEq α] (b : Bucket α β)
    (i : Nat) (key q : α) (value : β) :
    HasKey q (insertAt b i key value).node ↔ q = key ∨ HasKey q b.node := by
  rw [insertAt]
  split
  · rename_i hi
    by_cases hk : key = b.keys[i]
    · simp only [hk, BEq.rfl, ↓reduceIte, Bucket.node, hasKey_collision, Array.set_getElem_self]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact Array.mem_iff_getElem.mpr ⟨i, hi, rfl⟩
        · exact h
    · simp only [show (key == b.keys[i]) = false by simp [hk], Bool.false_eq_true, ↓reduceIte]
      exact insertAt_mem b (i + 1) key q value
  · simp [Bucket.node, or_comm]
termination_by b.keys.size - i

theorem DistinctKeys.push {keys : Array α} (hu : DistinctKeys keys)
    {key : α} (fresh : key ∉ keys) : DistinctKeys (keys.push key) := by
  intro i hi j hj he
  by_cases hi' : i < keys.size <;> by_cases hj' : j < keys.size
  · exact hu i hi' j hj' (by simpa [Array.getElem_push, hi', hj'] using he)
  · have hjEq : j = keys.size := by simp only [Array.size_push] at hj; omega
    subst j
    have hkey : keys[i] = key := by simpa [Array.getElem_push, hi'] using he
    exact False.elim (fresh (Array.mem_iff_getElem.mpr ⟨i, hi', hkey⟩))
  · have hiEq : i = keys.size := by simp only [Array.size_push] at hi; omega
    subst i
    have hkey : keys[j] = key := by simpa [Array.getElem_push, hj'] using he.symm
    exact False.elim (fresh (Array.mem_iff_getElem.mpr ⟨j, hj', hkey⟩))
  · simp only [Array.size_push] at hi hj
    omega

theorem bucket_push_binding (b : Bucket α β) (key q : α) (value w : β) :
    HasBinding q w (Bucket.node ⟨b.keys.push key, b.vals.push value, by simp [b.size_eq]⟩) ↔
      (q = key ∧ w = value) ∨ HasBinding q w b.node := by
  simp only [Bucket.node, hasBinding_collision, Array.size_push]
  constructor
  · rintro ⟨i, hi, hk, hv⟩
    by_cases hi' : i < b.keys.size
    · exact Or.inr ⟨i, hi', by simpa [Array.getElem_push, hi'] using hk,
        by simpa [Array.getElem_push, b.size_eq ▸ hi'] using hv⟩
    · have : i = b.keys.size := by omega
      subst i
      exact Or.inl ⟨by simpa using hk.symm, by simpa [b.size_eq] using hv.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨i, hi, hk, hv⟩)
    · exact ⟨b.keys.size, by omega, by simp, by simp [b.size_eq]⟩
    · exact ⟨i, by omega, by simpa [Array.getElem_push, hi] using hk,
        by simpa [Array.getElem_push, b.size_eq ▸ hi] using hv⟩

theorem insertAt_unique_updated [BEq α] [LawfulBEq α] (b : Bucket α β)
    (hu : DistinctKeys b.keys) (i : Nat) (key : α) (value : β)
    (scanned : ∀ (j : Nat) (hj : j < b.keys.size), j < i → b.keys[j] ≠ key) :
    Unique (insertAt b i key value).node ∧ Updated b.node (insertAt b i key value).node key value := by
  rw [insertAt]
  split
  · rename_i hi
    by_cases hk : key = b.keys[i]
    · simp only [show (key == b.keys[i]) = true by simp [hk], ↓reduceIte]
      have keys_same : b.keys.set i key = b.keys := by rw [hk]; simp
      constructor
      · apply Unique.collision
        simpa only [keys_same] using hu
      · intro q w
        simp only [Bucket.node, hasBinding_collision, Array.size_set, Array.getElem_set]
        constructor
        · rintro ⟨j, hj, hq, hw⟩
          by_cases hji : j = i
          · subst j; exact Or.inl ⟨by simpa using hq.symm, by simpa using hw.symm⟩
          · have hq' : b.keys[j] = q := by simpa [Ne.symm hji] using hq
            refine Or.inr ⟨?_, j, hj, hq', by simpa [Ne.symm hji] using hw⟩
            intro hqk
            exact hji (hu j hj i hi (hq'.trans (hqk.trans hk)))
        · rintro (⟨rfl, rfl⟩ | ⟨hne, j, hj, hq, hw⟩)
          · exact ⟨i, hi, by simp, by simp⟩
          · have hij : i ≠ j := by intro he; subst j; exact hne (hq.symm.trans hk.symm)
            exact ⟨j, hj, by simpa [hij] using hq, by simpa [hij] using hw⟩
    · simp only [show (key == b.keys[i]) = false by simp [hk], Bool.false_eq_true, ↓reduceIte]
      apply insertAt_unique_updated b hu (i + 1) key value
      intro j hj hji
      by_cases he : j = i
      · subst j; exact Ne.symm hk
      · exact scanned j hj (by omega)
  · rename_i hi
    have fresh : key ∉ b.keys := by
      intro h
      obtain ⟨j, hj, hk⟩ := Array.mem_iff_getElem.mp h
      exact scanned j hj (by omega) hk
    constructor
    · exact .collision (hu.push fresh)
    · intro q w
      rw [bucket_push_binding]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · refine Or.inr ⟨?_, h⟩
          intro he; subst q; exact fresh (by simpa [Bucket.node] using h.hasKey)
      · rintro (h | ⟨_, h⟩)
        · exact Or.inl h
        · exact Or.inr h
termination_by b.keys.size - i

theorem insertEntries_wf_mem [BEq α] [LawfulBEq α]
    (childInsert : Node α β → α → β → Node α β) (hashAt : α → USize)
    (es : Array (Entry α β (Node α β))) (key : α) (value : β)
    (wf : WellFormed hashAt (.entries es))
    (childSpec : ∀ (j : Nat) (hj : j < es.size) (child : Node α β), es[j] = .ref child →
      WellFormed (fun q => nextHash (hashAt q)) (childInsert child key value) ∧
        ∀ q, HasKey q (childInsert child key value) ↔ q = key ∨ HasKey q child) :
    WellFormed hashAt (.entries (insertEntries childInsert hashAt es key value)) ∧
      ∀ q, HasKey q (.entries (insertEntries childInsert hashAt es key value)) ↔
        q = key ∨ HasKey q (.entries es) := by
  have hi := wf.slot_lt (hashAt key)
  have finish (e : Entry α β (Node α β))
      (mem : ∀ q, EntryHasKey q e ↔ q = key ∨ EntryHasKey q es[slot (hashAt key)])
      (hc : ∀ n, e = .ref n → WellFormed (fun q => nextHash (hashAt q)) n) :
      WellFormed hashAt (.entries (es.set (slot (hashAt key)) e)) ∧
        ∀ q, HasKey q (.entries (es.set (slot (hashAt key)) e)) ↔
          q = key ∨ HasKey q (.entries es) := by
    constructor
    · apply wellFormed_set wf _ hi e _ hc
      intro q hq
      rcases (mem q).mp hq with rfl | hq
      · rfl
      · cases wf with | entries _ route _ => exact route _ hi q hq
    · exact hasKey_set_iff _ hi e key mem
  simp only [insertEntries, Array.modify, Array.modifyM, dif_pos hi, Id.run, bind, pure]
  cases he : es[slot (hashAt key)] with
  | null =>
    refine finish _ ?_ ?_
    · intro q; simp [EntryHasKey, he]
    · intro n hn; cases hn
  | entry k v =>
    by_cases hk : key = k
    · subst k
      simp only [BEq.rfl, ↓reduceIte]
      refine finish _ ?_ ?_
      · intro q; simp [EntryHasKey, he]
      · intro n hn; cases hn
    · simp only [show (key == k) = false by simp [hk], Bool.false_eq_true, ↓reduceIte]
      refine finish _ ?_ ?_
      · intro q; simp [EntryHasKey, he, or_comm]
      · intro n hn; cases hn; exact wellFormed_mkCollisionNode _ _ _ _ _
  | ref child =>
    obtain ⟨hw, hm⟩ := childSpec _ hi child he
    refine finish _ ?_ ?_
    · intro q; simpa [EntryHasKey, he] using hm q
    · intro n hn; cases hn; exact hw

theorem insertEntries_unique_updated [BEq α] [LawfulBEq α]
    (childInsert : Node α β → α → β → Node α β) (hashAt : α → USize)
    (es : Array (Entry α β (Node α β))) (key : α) (value : β)
    (wf : WellFormed hashAt (.entries es)) (hu : Unique (.entries es))
    (childSpec : ∀ (j : Nat) (hj : j < es.size) (child : Node α β), es[j] = .ref child →
      Unique child → Unique (childInsert child key value) ∧
        Updated child (childInsert child key value) key value) :
    Unique (.entries (insertEntries childInsert hashAt es key value)) ∧
      Updated (.entries es) (.entries (insertEntries childInsert hashAt es key value)) key value := by
  have hi := wf.slot_lt (hashAt key)
  have finish (e : Entry α β (Node α β))
      (hc : ∀ n, e = .ref n → Unique n)
      (upd : ∀ q w, EntryHasBinding q w e ↔
        (q = key ∧ w = value) ∨ (q ≠ key ∧ EntryHasBinding q w es[slot (hashAt key)])) :
      Unique (.entries (es.set (slot (hashAt key)) e)) ∧
        Updated (.entries es) (.entries (es.set (slot (hashAt key)) e)) key value :=
    ⟨unique_set hu _ hi e hc, updated_set wf key value hi e upd⟩
  simp only [insertEntries, Array.modify, Array.modifyM, dif_pos hi, Id.run, bind, pure]
  cases he : es[slot (hashAt key)] with
  | null =>
    refine finish _ ?_ ?_
    · intro n hn; cases hn
    · intro q w; simp [EntryHasBinding, he]
  | entry k v =>
    by_cases hk : key = k
    · subst k
      simp only [BEq.rfl, ↓reduceIte]
      refine finish _ ?_ ?_
      · intro n hn; cases hn
      · intro q w; simp only [EntryHasBinding, he]; grind
    · simp only [show (key == k) = false by simp [hk], Bool.false_eq_true, ↓reduceIte]
      refine finish _ ?_ ?_
      · intro n hn; cases hn; exact unique_mkCollisionNode (Ne.symm hk) _ _
      · intro q w
        simp only [EntryHasBinding, he, hasBinding_mkCollisionNode]
        grind
  | ref child =>
    have hchild : Unique child := by cases hu with | entries hc => exact hc _ hi child he
    obtain ⟨hu', hupd⟩ := childSpec _ hi child he hchild
    refine finish _ ?_ ?_
    · intro n hn; cases hn; exact hu'
    · intro q w; simpa [EntryHasBinding, he] using hupd q w

theorem insertNoExpand_entries [BEq α] (es : Array (Entry α β (Node α β)))
    (hashAt : α → USize) (key : α) (value : β) :
    insertNoExpand (.entries es) (hashAt key) key value =
      .entries (insertEntries (fun n k v => insertNoExpand n (nextHash (hashAt k)) k v)
        hashAt es key value) := by
  rw [insertNoExpand]
  simp only [insertEntries, Array.modify, Array.modifyM, Id.run, bind, pure]
  split
  · split <;> simp_all [Array.set_set]
  · rfl

theorem insertNoExpand_wf_mem [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α) (value : β) :
    WellFormed hashAt (insertNoExpand node (hashAt key) key value) ∧
      ∀ q, HasKey q (insertNoExpand node (hashAt key) key value) ↔ q = key ∨ HasKey q node := by
  induction wf generalizing key value with
  | collision hashAt keys vals hsz =>
    rw [insertNoExpand, insertCollision_eq ⟨keys, vals, hsz⟩]
    exact ⟨.collision _ _ _ _, fun q => insertAt_mem _ 0 key q value⟩
  | @entries hashAt es hs route children ih =>
    rw [insertNoExpand_entries]
    apply insertEntries_wf_mem _ _ _ _ _ (.entries hs route children)
    intro j hj child he
    exact ih j hj child he key value

theorem insertNoExpand_unique_updated [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (hu : Unique node) (key : α) (value : β) :
    Unique (insertNoExpand node (hashAt key) key value) ∧
      Updated node (insertNoExpand node (hashAt key) key value) key value := by
  induction wf generalizing key value with
  | collision hashAt keys vals hsz =>
    rw [insertNoExpand, insertCollision_eq ⟨keys, vals, hsz⟩]
    cases hu with
    | collision distinct => exact insertAt_unique_updated _ distinct 0 key value (by omega)
  | @entries hashAt es hs route children ih =>
    rw [insertNoExpand_entries]
    apply insertEntries_unique_updated _ _ _ _ _ (.entries hs route children) hu
    intro j hj child he hchild
    exact ih j hj child he hchild key value

theorem rebuild_wf_mem [BEq α] [LawfulBEq α]
    (childInsert : Node α β → α → β → Node α β) (hashAt : α → USize)
    (childSpec : ∀ n, WellFormed (fun q => nextHash (hashAt q)) n → ∀ k v,
      WellFormed (fun q => nextHash (hashAt q)) (childInsert n k v) ∧
        ∀ q, HasKey q (childInsert n k v) ↔ q = k ∨ HasKey q n)
    (b : Bucket α β) (i : Nat) (es : Array (Entry α β (Node α β)))
    (wf : WellFormed hashAt (.entries es)) :
    WellFormed hashAt (.entries (rebuild childInsert hashAt b i es)) ∧
      ∀ q, HasKey q (.entries (rebuild childInsert hashAt b i es)) ↔
        HasKey q (.entries es) ∨ ∃ (j : Nat) (hj : j < b.keys.size), i ≤ j ∧ b.keys[j] = q := by
  rw [rebuild]
  split
  · rename_i hi
    have step := insertEntries_wf_mem childInsert hashAt es b.keys[i]
      (b.vals[i]'(b.size_eq ▸ hi)) wf (by
        intro j hj child he
        cases wf with | entries _ _ hc => exact childSpec child (hc j hj child he) _ _)
    obtain ⟨hw, hm⟩ := rebuild_wf_mem childInsert hashAt childSpec b (i + 1) _ step.1
    refine ⟨hw, ?_⟩
    intro q
    rw [hm, step.2]
    constructor
    · rintro ((hk | hold) | ⟨j, hj, hij, hk⟩)
      · exact Or.inr ⟨i, hi, Nat.le_refl _, hk.symm⟩
      · exact Or.inl hold
      · exact Or.inr ⟨j, hj, by omega, hk⟩
    · rintro (hold | ⟨j, hj, hij, hk⟩)
      · exact Or.inl (Or.inr hold)
      · by_cases he : j = i
        · subst j; exact Or.inl (Or.inl hk.symm)
        · exact Or.inr ⟨j, hj, by omega, hk⟩
  · rename_i hi
    refine ⟨wf, ?_⟩
    intro q
    constructor
    · exact Or.inl
    · rintro (h | ⟨j, hj, hij, _⟩)
      · exact h
      · omega
termination_by b.keys.size - i

theorem insertNode_wf_mem [BEq α] [LawfulBEq α] (levels : Nat)
    (hashAt : α → USize) (node : Node α β) (wf : WellFormed hashAt node)
    (key : α) (value : β) :
    WellFormed hashAt (insertNode levels hashAt node key value) ∧
      ∀ q, HasKey q (insertNode levels hashAt node key value) ↔ q = key ∨ HasKey q node := by
  induction levels generalizing hashAt node key value with
  | zero => exact insertNoExpand_wf_mem wf key value
  | succ levels ih =>
    cases node with
    | entries es =>
      simp only [insertNode]
      apply insertEntries_wf_mem _ _ _ _ _ wf
      intro j hj child he
      cases wf with | entries _ _ hc => exact ih _ child (hc j hj child he) key value
    | collision keys vals hsz =>
      simp only [insertNode]
      split
      · exact ⟨.collision _ _ _ _, fun q => insertAt_mem _ 0 key q value⟩
      · have rebuilt := rebuild_wf_mem
          (insertNode levels (fun q => nextHash (hashAt q))) hashAt
          (fun n hn k v => ih _ n hn k v)
          (insertAt ⟨keys, vals, hsz⟩ 0 key value) 0 mkEmptyEntriesArray (wellFormed_empty _)
        refine ⟨rebuilt.1, ?_⟩
        intro q
        rw [rebuilt.2]
        have empty : ¬ HasKey q (mkEmptyEntries : Node α β) := by
          simp [mkEmptyEntries, hasKey_entries, mkEmptyEntriesArray, EntryHasKey]
        simp only [show ¬ HasKey q (.entries (mkEmptyEntriesArray : Array (Entry α β (Node α β)))) from empty,
          false_or, Nat.zero_le, true_and]
        rw [← Array.mem_iff_getElem]
        simpa only [Bucket.node, hasKey_collision] using
          (insertAt_mem ⟨keys, vals, hsz⟩ 0 key q value)

/-- Rebuilding preserves every binding of a distinct bucket. The accumulator
must not already contain a key in the unprocessed suffix. -/
theorem rebuild_unique_bindings [BEq α] [LawfulBEq α]
    (childInsert : Node α β → α → β → Node α β) (hashAt : α → USize)
    (childWF : ∀ n, WellFormed (fun q => nextHash (hashAt q)) n → ∀ k v,
      WellFormed (fun q => nextHash (hashAt q)) (childInsert n k v) ∧
        ∀ q, HasKey q (childInsert n k v) ↔ q = k ∨ HasKey q n)
    (childUpd : ∀ n, WellFormed (fun q => nextHash (hashAt q)) n → Unique n → ∀ k v,
      Unique (childInsert n k v) ∧ Updated n (childInsert n k v) k v)
    (b : Bucket α β) (distinct : DistinctKeys b.keys) (i : Nat)
    (es : Array (Entry α β (Node α β)))
    (wf : WellFormed hashAt (.entries es)) (hu : Unique (.entries es))
    (disjoint : ∀ (j : Nat) (hj : j < b.keys.size), i ≤ j → ¬ HasKey b.keys[j] (.entries es)) :
    Unique (.entries (rebuild childInsert hashAt b i es)) ∧
      ∀ q w, HasBinding q w (.entries (rebuild childInsert hashAt b i es)) ↔
        HasBinding q w (.entries es) ∨
          ∃ (j : Nat) (hj : j < b.keys.size), i ≤ j ∧ b.keys[j] = q ∧ b.vals[j]'(b.size_eq ▸ hj) = w := by
  rw [rebuild]
  split
  · rename_i hi
    have stepWM := insertEntries_wf_mem childInsert hashAt es b.keys[i]
      (b.vals[i]'(b.size_eq ▸ hi)) wf (by
        intro j hj child he
        cases wf with | entries _ _ hc => exact childWF child (hc j hj child he) _ _)
    have stepUV := insertEntries_unique_updated childInsert hashAt es b.keys[i]
      (b.vals[i]'(b.size_eq ▸ hi)) wf hu (by
        intro j hj child he hu'
        cases wf with | entries _ _ hc => exact childUpd child (hc j hj child he) hu' _ _)
    have nextDisjoint : ∀ (j : Nat) (hj : j < b.keys.size), i + 1 ≤ j →
        ¬ HasKey b.keys[j] (.entries (insertEntries childInsert hashAt es b.keys[i]
          (b.vals[i]'(b.size_eq ▸ hi)))) := by
      intro j hj hij hmem
      rcases (stepWM.2 _).mp hmem with he | hold
      · have := distinct j hj i hi he
        omega
      · exact disjoint j hj (by omega) hold
    obtain ⟨hu', hb'⟩ := rebuild_unique_bindings childInsert hashAt childWF childUpd
      b distinct (i + 1) _ stepWM.1 stepUV.1 nextDisjoint
    refine ⟨hu', ?_⟩
    intro q w
    rw [hb', stepUV.2]
    constructor
    · rintro ((⟨hk, hv⟩ | ⟨_, hold⟩) | ⟨j, hj, hij, hk, hv⟩)
      · exact Or.inr ⟨i, hi, Nat.le_refl _, hk.symm, hv.symm⟩
      · exact Or.inl hold
      · exact Or.inr ⟨j, hj, by omega, hk, hv⟩
    · rintro (hold | ⟨j, hj, hij, hk, hv⟩)
      · refine Or.inl (Or.inr ⟨?_, hold⟩)
        intro he
        subst q
        exact disjoint i hi (Nat.le_refl _) hold.hasKey
      · by_cases he : j = i
        · subst j; exact Or.inl (Or.inl ⟨hk.symm, hv.symm⟩)
        · exact Or.inr ⟨j, hj, by omega, hk, hv⟩
  · rename_i hi
    refine ⟨hu, ?_⟩
    intro q w
    constructor
    · exact Or.inl
    · rintro (h | ⟨j, hj, hij, _, _⟩)
      · exact h
      · omega
termination_by b.keys.size - i

theorem insertNode_unique_updated [BEq α] [LawfulBEq α] (levels : Nat)
    (hashAt : α → USize) (node : Node α β) (wf : WellFormed hashAt node) (hu : Unique node)
    (key : α) (value : β) :
    Unique (insertNode levels hashAt node key value) ∧
      Updated node (insertNode levels hashAt node key value) key value := by
  induction levels generalizing hashAt node key value with
  | zero => exact insertNoExpand_unique_updated wf hu key value
  | succ levels ih =>
    cases node with
    | entries es =>
      simp only [insertNode]
      apply insertEntries_unique_updated _ _ _ _ _ wf hu
      intro j hj child he hu'
      cases wf with | entries _ _ hc => exact ih _ child (hc j hj child he) hu' key value
    | collision keys vals hsz =>
      have distinct : DistinctKeys keys := by cases hu with | collision h => exact h
      have bucketUV := insertAt_unique_updated ⟨keys, vals, hsz⟩ distinct 0 key value (by omega)
      simp only [insertNode]
      split
      · exact bucketUV
      · have distinct' : DistinctKeys (insertAt ⟨keys, vals, hsz⟩ 0 key value).keys := by
          cases bucketUV.1 with | collision h => exact h
        have rebuilt := rebuild_unique_bindings
          (insertNode levels (fun q => nextHash (hashAt q))) hashAt
          (fun n hn k v => insertNode_wf_mem levels _ n hn k v)
          (fun n hn un k v => ih _ n hn un k v)
          (insertAt ⟨keys, vals, hsz⟩ 0 key value) distinct' 0 mkEmptyEntriesArray
          (wellFormed_empty _) unique_empty (by
            intro j hj hij
            simp [hasKey_entries, mkEmptyEntriesArray, EntryHasKey])
        refine ⟨rebuilt.1, ?_⟩
        intro q w
        rw [rebuilt.2]
        have empty : ¬ HasBinding q w (.entries (mkEmptyEntriesArray : Array (Entry α β (Node α β)))) := by
          simp [hasBinding_entries, mkEmptyEntriesArray, EntryHasBinding]
        simp only [empty, false_or, Nat.zero_le, true_and]
        rw [← hasBinding_collision]
        exact bucketUV.2 q w

/-- Insertion preserves the routing invariant even when the input has duplicate keys. -/
theorem valid_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) (value : β) :
    Valid (insert map key value) := by
  simpa only [Valid, insert_root_eq] using (insertNode_wf_mem _ _ map.root wf key value).1

/-- Exact membership update; uniqueness is not needed. -/
theorem mem_insert_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key q : α) (value : β) :
    Mem q (insert map key value) ↔ q = key ∨ Mem q map := by
  simpa only [Mem, insert_root_eq] using (insertNode_wf_mem _ _ map.root wf key value).2 q

theorem unique_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) : Unique (insert map key value).root := by
  simpa only [insert_root_eq] using (insertNode_unique_updated _ _ map.root wf hu key value).1

/-- Abstract map binding, defined by the stored keys and values rather than lookup. -/
def MapsTo [BEq α] [Hashable α] (key : α) (value : β)
    (map : Lean.PersistentHashMap α β) : Prop := HasBinding key value map.root

/-- The complete key/value update law. Replacing a key discards its old binding;
all other bindings are preserved. `Unique` rules out duplicate collision keys. -/
theorem mapsTo_insert_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value w : β) :
    MapsTo q w (insert map key value) ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ MapsTo q w map) := by
  simpa only [MapsTo, insert_root_eq] using (insertNode_unique_updated _ _ map.root wf hu key value).2 q w

@[scoped simp] theorem mapsTo_insert_self [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value w : β) : MapsTo key w (insert map key value) ↔ w = value := by
  simp [mapsTo_insert_iff map wf hu]

theorem mapsTo_insert_of_ne [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value w : β) (hne : q ≠ key) :
    MapsTo q w (insert map key value) ↔ MapsTo q w map := by
  simp [mapsTo_insert_iff map wf hu, hne]

/-- The previously proved lookup composes with the verified insertion. -/
theorem contains_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key q : α) (value : β) :
    contains (insert map key value) q = ((q == key) || contains map q) := by
  apply Bool.eq_iff_iff.mpr
  rw [contains_eq_true_iff _ (valid_insert map wf key value), mem_insert_iff map wf]
  simp [contains_eq_true_iff map wf]

@[scoped simp] theorem contains_insert_self [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) (value : β) :
    contains (insert map key value) key = true := by
  simp [contains_insert map wf]

/-- Starting with the native empty map, every finite sequence of these insertions
has both invariants required by the key/value theorem. -/
theorem insert_fold_valid_unique [BEq α] [LawfulBEq α] [Hashable α]
    (bindings : List (α × β)) :
    let map := bindings.foldl (fun m kv => insert m kv.1 kv.2) Lean.PersistentHashMap.empty
    Valid map ∧ Unique map.root := by
  have preserve (xs : List (α × β)) (map : Lean.PersistentHashMap α β)
      (wf : Valid map) (hu : Unique map.root) :
      Valid (xs.foldl (fun m kv => insert m kv.1 kv.2) map) ∧
        Unique (xs.foldl (fun m kv => insert m kv.1 kv.2) map).root := by
    induction xs generalizing map with
    | nil => exact ⟨wf, hu⟩
    | cons kv xs ih => exact ih _ (valid_insert map wf _ _) (unique_insert map wf hu _ _)
  exact preserve bindings _ valid_empty unique_empty

end HAMTVerify
