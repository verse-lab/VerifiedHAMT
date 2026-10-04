module

public import HAMTVerify.SetWithoutValArray.Insert

@[expose] public section

/-! Routing and membership proofs adapted from HAMTVerify.InsertProofs. -/
namespace HAMTVerify.SetWithoutValArray.Raw

open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

section Util

-- FIXME: Should not hardcode these constants
theorem hash_shift_offset (h offset : USize) (bound : offset.toNat + 5 ≤ 30) :
    h >>> (offset + shift) = nextHash (h >>> offset) := by
  change h >>> (offset + 5) = (h >>> offset) >>> (5 : USize)
  apply USize.toNat_inj.mp
  rcases System.Platform.numBits_eq with hb | hb
  all_goals
    simp only [USize.toNat_shiftRight, USize.toNat_add, USize.toNat_ofNat, hb]
    have ho : offset.toNat < System.Platform.numBits := by omega
    have hs : offset.toNat + 5 < System.Platform.numBits := by omega
    simp only [hb] at ho hs
    simp only [Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega : offset.toNat + 5 < _), Nat.mod_eq_of_lt hs,
      Nat.mod_eq_of_lt ho, Nat.shiftRight_add]

theorem offset_add_shift (offset : USize) (bound : offset.toNat + 5 ≤ 30) :
    (offset + shift).toNat = offset.toNat + 5 := by
  change (offset + 5).toNat = offset.toNat + 5
  rcases System.Platform.numBits_eq with hb | hb <;>
    simp only [USize.toNat_add, USize.toNat_ofNat, hb, Nat.reducePow, Nat.reduceMod] <;>
    exact Nat.mod_eq_of_lt (by omega)

end Util

theorem insertCollisionAux_mem [BEq α] [LawfulBEq α]
    (keys : Array α)
    (i : Nat) (key q : α) :
    HasKey q (insertCollisionAux ⟨.collision keys, .mk ..⟩ i key).val ↔
      q = key ∨ HasKey q (.collision keys) := by
  rw [insertCollisionAux.eq_def]
  dsimp only
  split
  · rename_i hi
    split
    · grind [hasKey_collision, Array.set_getElem_self]
    · exact insertCollisionAux_mem keys (i + 1) key q
  · simp [or_comm]
termination_by keys.size - i


theorem insertEntries_wf_mem [BEq α] [LawfulBEq α]
    (hashAt : α → USize) (es : Array (Entry α (Node α)))
    (childInsert : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (key : α)
    (wf : WellFormed hashAt (.entries es))
    (childSpec : ∀ (child : Node α) (hmem : .ref child ∈ es),
      letI res := (childInsert child hmem (nextHash (hashAt key)) key)
      WellFormed (fun q => nextHash (hashAt q)) res ∧
        ∀ q, HasKey q res ↔
          q = key ∨ HasKey q child) :
    letI res := insertEntries es childInsert (hashAt key) key
    WellFormed hashAt (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        q = key ∨ HasKey q (.entries es) := by
  have hi := wf.slot_lt (hashAt key)
  have finish (e : Entry α (Node α))
      (mem : ∀ q, EntryHasKey q e ↔ q = key ∨ EntryHasKey q es[slot (hashAt key)])
      (hc : ∀ n, e = .ref n → WellFormed (fun q => nextHash (hashAt q)) n) :
      letI res := (.entries (es.set (slot (hashAt key)) e))
      WellFormed hashAt res ∧
        ∀ q, HasKey q res ↔
          q = key ∨ HasKey q (.entries es) := by
    constructor
    · apply wellFormed_set wf _ hi e _ hc
      cases wf <;> grind
    · exact hasKey_set_iff _ hi e key mem
  rw [insertEntries_eq _ _ _ _ hi]
  split
  · apply finish <;> grind [EntryHasKey]
  · split <;> apply finish <;>
      grind [EntryHasKey, hasKey_mkCollisionNode, wellFormed_mkCollisionNode]
  · rename_i child hmem he _
    have := childSpec child hmem
    apply finish <;> grind [EntryHasKey]


theorem insertNoExpand_wf_mem [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α} (wf : WellFormed hashAt node) (key : α) :
    letI res := insertNoExpand node (hashAt key) key
    WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by
  induction wf generalizing key with
  | collision hashAt keys =>
    rw [insertNoExpand.eq_def]
    exact ⟨wellFormed_collisionNode _ _, fun q => insertCollisionAux_mem keys 0 key q⟩
  | @entries hashAt es hs route children ih =>
    rw [insertNoExpand.eq_def]
    apply insertEntries_wf_mem hashAt es _ key (.entries hs route children)
    grind [Array.mem_iff_getElem]


theorem rebuild_wf_mem [BEq α] [LawfulBEq α] [Hashable α]
    (childInsert : Node α → USize → α → Node α) (offset : USize)
    (childSpec :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k,
        letI res := childInsert n (hashAt k) k
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (keys : Array α)
    (i : Nat) (es : Array (Entry α (Node α)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es)) :
    letI res := rebuild childInsert offset ⟨.collision keys, .mk ..⟩ i es
    WellFormed (fun q => (hash q).toUSize >>> offset) (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        HasKey q (.entries es) ∨ ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = q := by
  rw [rebuild.eq_def]
  dsimp only
  split
  · rename_i hi
    have step := insertEntries_wf_mem (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i]
      wf (by
        cases wf <;> grind [Array.mem_iff_getElem])
    obtain ⟨hw, hm⟩ := rebuild_wf_mem childInsert offset childSpec keys (i + 1) _ step.1
    refine ⟨hw, ?_⟩
    intro q
    rw [hm, step.2]
    grind
  · exact ⟨wf, by grind⟩
termination_by keys.size - i

/-- Insertion preserves routing and membership for the hash at the current offset.
The bound keeps the offset arithmetic valid on both 32-bit and 64-bit platforms. -/
theorem insertNode_wf_mem [BEq α] [LawfulBEq α] [Hashable α] (levels : Nat)
    (offset : USize) (bound : offset.toNat + 5 * levels ≤ 30)
    (node : Node α) (wf : WellFormed (fun k => (hash k).toUSize >>> offset) node)
    (key : α) :
    letI res := insertNode levels offset node ((hash key).toUSize >>> offset) key
    WellFormed (fun k => (hash k).toUSize >>> offset) res ∧
      ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by
  induction levels generalizing offset node key with
  | zero => exact insertNoExpand_wf_mem wf key
  | succ levels ih =>
    have hb : offset.toNat + 5 ≤ 30 := by omega
    have hn : (offset + shift).toNat + 5 * levels ≤ 30 := by
      rw [offset_add_shift offset hb]
      omega
    have childSpec := ih (offset + shift) hn
    simp only [hash_shift_offset _ offset hb] at childSpec
    cases node with
    | entries es =>
      simp only [insertNode]
      apply insertEntries_wf_mem _ es _ key wf
      cases wf <;> grind [Array.mem_iff_getElem]
    | collision keys =>
      simp only [insertNode]
      generalize hc : insertCollision keys key = b
      have hm (q : α) : HasKey q b.val ↔ q = key ∨ HasKey q (.collision keys) := by
        rw [← hc]
        exact insertCollisionAux_mem keys 0 key q
      obtain ⟨node, hb⟩ := b
      cases hb with
      | mk keys' =>
        simp only [getCollisionNodeSize]
        split
        · exact ⟨.collision _ _, hm⟩
        · have rebuilt := rebuild_wf_mem (insertNode levels (offset + shift)) offset childSpec
            keys' 0 mkEmptyEntriesArray (wellFormed_empty _)
          refine ⟨rebuilt.1, ?_⟩
          intro q
          rw [rebuilt.2]
          simpa [hasKey_entries, mkEmptyEntriesArray, EntryHasKey, ← Array.mem_iff_getElem] using hm q


private theorem root_offset_bound : (0 : USize).toNat + 5 * (maxDepth.toNat - 1) ≤ 30 := by
  rcases System.Platform.numBits_eq with hb | hb <;>
    simp [maxDepth, USize.toNat_ofNat, hb]

/-- Insertion preserves the routing invariant even when the input has duplicate keys. -/
theorem valid_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key : α) :
    Valid (insert map key) := by
  simpa [Valid, insert] using
    (insertNode_wf_mem (maxDepth.toNat - 1) 0 root_offset_bound map.root
      (by simpa [Valid] using wf) key).1

/-- Exact membership update; uniqueness is not needed. -/
theorem mem_insert_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key q : α) :
    Mem q (insert map key) ↔ q = key ∨ Mem q map := by
  simpa [Mem, insert] using
    (insertNode_wf_mem (maxDepth.toNat - 1) 0 root_offset_bound map.root
      (by simpa [Valid] using wf) key).2 q


/-- The previously proved lookup composes with the verified insertion. -/
theorem contains_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key q : α) :
    contains (insert map key) q = ((q == key) || contains map q) := by
  apply Bool.eq_iff_iff.mpr
  rw [contains_eq_true_iff _ (valid_insert map wf key), mem_insert_iff map wf]
  simp [contains_eq_true_iff map wf]

@[scoped simp] theorem contains_insert_self [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key : α) :
    contains (insert map key) key = true := by
  simp [contains_insert map wf]


end HAMTVerify.SetWithoutValArray.Raw
