module

public import HAMTVerify.SetWithoutValArray.InsertProofs
public import HAMTVerify.SetWithoutValArray.Size

@[expose] public section

/-! Uniqueness and key-count preservation, adapted from HAMTVerify.InsertProofs.
Without value bindings, rebuilding needs only the invariant-preservation part. -/

namespace HAMTVerify.SetWithoutValArray.Raw

open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem insertCollisionAux_unique [BEq α] [LawfulBEq α] (keys : Array α)
    (hu : DistinctKeys keys) (i : Nat) (key : α)
    (scanned : ∀ (j : Nat) (hj : j < keys.size), j < i → keys[j] ≠ key) :
    Unique (insertCollisionAux ⟨.collision keys, .mk ..⟩ i key).val := by
  rw [insertCollisionAux.eq_def]
  dsimp only
  split
  · rename_i hi
    split
    · apply Unique.collision
      grind [Array.set_getElem_self]
    · apply insertCollisionAux_unique keys hu (i + 1) key
      grind
  · have fresh : key ∉ keys := by grind [Array.mem_iff_getElem]
    exact .collision (hu.push fresh)
termination_by keys.size - i

theorem insertEntries_unique [BEq α] [LawfulBEq α]
    (hashAt : α → USize) (es : Array (Entry α (Node α)))
    (childInsert : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (key : α) (wf : WellFormed hashAt (.entries es)) (hu : Unique (.entries es))
    (childSpec : ∀ (child : Node α) (hmem : .ref child ∈ es), Unique child →
      Unique (childInsert child hmem (nextHash (hashAt key)) key)) :
    Unique (.entries (insertEntries es childInsert (hashAt key) key)) := by
  have hi := wf.slot_lt (hashAt key)
  rw [insertEntries_eq _ _ _ _ hi]
  split
  · apply unique_set hu <;> grind
  · split <;> apply unique_set hu <;> grind [unique_mkCollisionNode]
  · rename_i child hmem he _
    have hchild : Unique child := by cases hu <;> grind
    apply unique_set hu <;> grind

theorem insertNoExpand_unique [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α} (wf : WellFormed hashAt node) (hu : Unique node) (key : α) :
    Unique (insertNoExpand node (hashAt key) key) := by
  induction wf generalizing key with
  | collision hashAt keys =>
    rw [insertNoExpand.eq_def]
    cases hu with
    | collision distinct => exact insertCollisionAux_unique keys distinct 0 key (by omega)
  | @entries hashAt es hs route children ih =>
    rw [insertNoExpand.eq_def]
    apply insertEntries_unique hashAt es _ key (.entries hs route children) hu
    grind [Array.mem_iff_getElem]

theorem rebuild_unique [BEq α] [LawfulBEq α] [Hashable α]
    (childInsert : Node α → USize → α → Node α) (offset : USize)
    (childWF :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k,
        letI res := childInsert n (hashAt k) k
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (childUnique :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → Unique n → ∀ k, Unique (childInsert n (hashAt k) k))
    (keys : Array α) (i : Nat) (es : Array (Entry α (Node α)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es))
    (hu : Unique (.entries es)) :
    Unique (.entries (rebuild childInsert offset ⟨.collision keys, .mk ..⟩ i es)) := by
  rw [rebuild.eq_def]
  dsimp only
  split
  · rename_i hi
    have stepWF := insertEntries_wf_mem (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i] wf (by
        cases wf <;> grind [Array.mem_iff_getElem])
    have stepUnique := insertEntries_unique (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i] wf hu (by
        cases wf <;> grind [Array.mem_iff_getElem])
    exact rebuild_unique childInsert offset childWF childUnique keys (i + 1) _ stepWF.1 stepUnique
  · exact hu
termination_by keys.size - i

theorem insertNode_unique [BEq α] [LawfulBEq α] [Hashable α] (levels : Nat)
    (offset : USize) (bound : offset.toNat + 5 * levels ≤ 30)
    (node : Node α) (wf : WellFormed (fun k => (hash k).toUSize >>> offset) node)
    (hu : Unique node) (key : α) :
    Unique (insertNode levels offset node ((hash key).toUSize >>> offset) key) := by
  induction levels generalizing offset node key with
  | zero => exact insertNoExpand_unique wf hu key
  | succ levels ih =>
    have hb : offset.toNat + 5 ≤ 30 := by omega
    have hn : (offset + shift).toNat + 5 * levels ≤ 30 := by
      rw [offset_add_shift offset hb]
      omega
    have childWF := insertNode_wf_mem (α := α) levels (offset + shift) hn
    have childUnique := ih (offset + shift) hn
    simp only [hash_shift_offset _ offset hb] at childWF childUnique
    cases node with
    | entries es =>
      simp only [insertNode]
      apply insertEntries_unique _ es _ key wf hu
      cases wf <;> grind [Array.mem_iff_getElem]
    | collision keys =>
      have distinct : DistinctKeys keys := by cases hu with | collision h => exact h
      have ub := insertCollisionAux_unique keys distinct 0 key (by omega)
      rw [← insertCollision.eq_def] at ub
      simp only [insertNode]
      generalize hc : insertCollision keys key = b at ub ⊢
      obtain ⟨node, hb⟩ := b
      cases hb with
      | mk keys' =>
        simp only [getCollisionNodeSize]
        split
        · exact ub
        · exact rebuild_unique (insertNode levels (offset + shift)) offset
            childWF childUnique keys' 0 mkEmptyEntriesArray (wellFormed_empty _) unique_empty

theorem unique_insert [BEq α] [LawfulBEq α] [Hashable α]
    (set : Raw α) (wf : Valid set) (hu : Unique set.root) (key : α) :
    Unique (insert set key).root := by
  have bound : (0 : USize).toNat + 5 * (maxDepth.toNat - 1) ≤ 30 := by
    rcases System.Platform.numBits_eq with hb | hb <;> simp [maxDepth, USize.toNat_ofNat, hb]
  simpa [insert] using insertNode_unique (maxDepth.toNat - 1) 0 bound set.root
    (by simpa [Valid] using wf) hu key

/-- Duplicate-free lists with the same members have equal lengths. -/
private theorem length_eq_of_nodup_of_mem_iff [BEq α] [LawfulBEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁.length = l₂.length :=
  (List.perm_iff_count.mpr fun a => by simp only [h₁.count, h₂.count, h a]).length_eq

theorem keyCount_insert [BEq α] [LawfulBEq α] [Hashable α]
    (set : Raw α) (wf : Valid set) (hu : Unique set.root) (key : α) :
    keyCount (insert set key).root =
      if contains set key then keyCount set.root else keyCount set.root + 1 := by
  have wf' := valid_insert set wf key
  have hnodup := nodup_keyList wf hu
  have hnodup' := nodup_keyList wf' (unique_insert set wf hu key)
  have hmem : ∀ q, q ∈ keyList (insert set key).root ↔ q = key ∨ q ∈ keyList set.root := by
    intro q
    rw [mem_keyList wf' q, mem_keyList wf q]
    exact mem_insert_iff set wf key q
  unfold keyCount
  split
  · rename_i hc
    have hk : key ∈ keyList set.root :=
      (mem_keyList wf key).mpr ((contains_eq_true_iff set wf key).mp hc)
    apply length_eq_of_nodup_of_mem_iff hnodup' hnodup
    grind
  · rename_i hc
    have hk : key ∉ keyList set.root := fun h =>
      hc ((contains_eq_true_iff set wf key).mpr ((mem_keyList wf key).mp h))
    rw [← List.length_cons]
    apply length_eq_of_nodup_of_mem_iff hnodup' (List.nodup_cons.mpr ⟨hk, hnodup⟩)
    grind

end HAMTVerify.SetWithoutValArray.Raw
