module

public import VerifiedHAMT.Insert
public import VerifiedHAMT.Size
public import VerifiedHAMT.Util
import all Lean.Data.PersistentHashMap
import all Init.Data.Array.Basic

@[expose] public section

/-! Correctness of the total insertion implementation on native nodes. -/

namespace VerifiedHAMT

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

theorem insertCollisionAux_mem [BEq α] [LawfulBEq α]
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (i : Nat) (key q : α) (value : β) :
    HasKey q (insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ i key value).val ↔
      q = key ∨ HasKey q (.collision keys vals hsz) := by
  rw [insertCollisionAux.eq_def]
  dsimp only
  split
  · rename_i hi
    split
    · grind [hasKey_collision, Array.set_getElem_self]
    · exact insertCollisionAux_mem keys vals hsz (i + 1) key q value
  · simp [or_comm]
termination_by keys.size - i

theorem insertCollisionAux_unique_updated [BEq α] [LawfulBEq α] (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (hu : DistinctKeys keys) (i : Nat) (key : α) (value : β)
    (scanned : ∀ (j : Nat) (hj : j < keys.size), j < i → keys[j] ≠ key) :
    letI res := insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ i key value
    Unique res.val ∧ Updated (.collision keys vals hsz) res.val key value := by
  rw [insertCollisionAux.eq_def]
  dsimp only
  split
  · rename_i hi
    split
    · constructor
      · apply Unique.collision
        grind [Array.set_getElem_self]
      · intro q w
        simp only [hasBinding_collision, Array.size_set, Array.getElem_set]
        grind [DistinctKeys]
    · apply insertCollisionAux_unique_updated keys vals hsz hu (i + 1) key value
      grind
  · rename_i hi
    have fresh : key ∉ keys := by grind [Array.mem_iff_getElem]
    constructor
    · exact .collision (hu.push fresh)
    · intro q w
      rw [collision_push_binding keys vals hsz]
      grind [→ HasBinding.hasKey, hasKey_collision]
termination_by keys.size - i

theorem insertEntries_wf_mem [BEq α] [LawfulBEq α]
    (hashAt : α → USize) (es : Array (Entry α β (Node α β)))
    (childInsert : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (key : α) (value : β)
    (wf : WellFormed hashAt (.entries es))
    (childSpec : ∀ (child : Node α β) (hmem : .ref child ∈ es),
      letI res := (childInsert child hmem (nextHash (hashAt key)) key value)
      WellFormed (fun q => nextHash (hashAt q)) res ∧
        ∀ q, HasKey q res ↔
          q = key ∨ HasKey q child) :
    letI res := insertEntries es childInsert (hashAt key) key value
    WellFormed hashAt (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        q = key ∨ HasKey q (.entries es) := by
  have hi := wf.slot_lt (hashAt key)
  have finish (e : Entry α β (Node α β))
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
  rw [insertEntries_eq _ _ _ _ _ hi]
  split
  · apply finish <;> grind [EntryHasKey]
  · split <;> apply finish <;>
      grind [EntryHasKey, hasKey_mkCollisionNode, wellFormed_mkCollisionNode]
  · rename_i child hmem he _
    have := childSpec child hmem
    apply finish <;> grind [EntryHasKey]

theorem insertEntries_unique_updated [BEq α] [LawfulBEq α]
    (hashAt : α → USize) (es : Array (Entry α β (Node α β)))
    (childInsert : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (key : α) (value : β)
    (wf : WellFormed hashAt (.entries es)) (hu : Unique (.entries es))
    (childSpec : ∀ (child : Node α β) (hmem : .ref child ∈ es),
      letI res := childInsert child hmem (nextHash (hashAt key)) key value
      Unique child → Unique res ∧ Updated child res key value) :
    letI res := insertEntries es childInsert (hashAt key) key value
    Unique (.entries res) ∧ Updated (.entries es) (.entries res) key value := by
  have hi := wf.slot_lt (hashAt key)
  have finish (e : Entry α β (Node α β))
      (hc : ∀ n, e = .ref n → Unique n)
      (upd : ∀ q w, EntryHasBinding q w e ↔
        (q = key ∧ w = value) ∨ (q ≠ key ∧ EntryHasBinding q w es[slot (hashAt key)])) :
      letI res := .entries (es.set (slot (hashAt key)) e)
      Unique res ∧ Updated (.entries es) res key value :=
    ⟨unique_set hu _ hi e hc, updated_set wf key value hi e upd⟩
  rw [insertEntries_eq _ _ _ _ _ hi]
  split
  · apply finish <;> grind [EntryHasBinding]
  · split <;> apply finish <;>
      grind [EntryHasBinding, hasBinding_mkCollisionNode, unique_mkCollisionNode]
  · rename_i child hmem he _
    have hchild : Unique child := by cases hu <;> grind
    have := childSpec child hmem hchild
    apply finish <;> grind [EntryHasBinding, Updated]

theorem insertNoExpand_wf_mem [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α) (value : β) :
    letI res := insertNoExpand node (hashAt key) key value
    WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by
  induction wf generalizing key value with
  | collision hashAt keys vals hsz =>
    rw [insertNoExpand.eq_def]
    exact ⟨wellFormed_collisionNode _ _, fun q => insertCollisionAux_mem keys vals hsz 0 key q value⟩
  | @entries hashAt es hs route children ih =>
    rw [insertNoExpand.eq_def]
    apply insertEntries_wf_mem hashAt es _ key value (.entries hs route children)
    grind [Array.mem_iff_getElem]

theorem insertNoExpand_unique_updated [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (hu : Unique node) (key : α) (value : β) :
    letI res := insertNoExpand node (hashAt key) key value
    Unique res ∧ Updated node res key value := by
  induction wf generalizing key value with
  | collision hashAt keys vals hsz =>
    rw [insertNoExpand.eq_def]
    cases hu with
    | collision distinct =>
      exact insertCollisionAux_unique_updated keys vals hsz distinct 0 key value (by omega)
  | @entries hashAt es hs route children ih =>
    rw [insertNoExpand.eq_def]
    apply insertEntries_unique_updated hashAt es _ key value (.entries hs route children) hu
    grind [Array.mem_iff_getElem]

theorem rebuild_wf_mem [BEq α] [LawfulBEq α] [Hashable α]
    (childInsert : Node α β → USize → α → β → Node α β) (offset : USize)
    (childSpec :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k v,
        letI res := childInsert n (hashAt k) k v
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (i : Nat) (es : Array (Entry α β (Node α β)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es)) :
    letI res := rebuild childInsert offset ⟨.collision keys vals hsz, .mk ..⟩ i es
    WellFormed (fun q => (hash q).toUSize >>> offset) (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        HasKey q (.entries es) ∨ ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = q := by
  rw [rebuild.eq_def]
  dsimp only
  split
  · rename_i hi
    have step := insertEntries_wf_mem (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i]
      (vals[i]'(hsz ▸ hi)) wf (by
        cases wf <;> grind [Array.mem_iff_getElem])
    obtain ⟨hw, hm⟩ := rebuild_wf_mem childInsert offset childSpec keys vals hsz (i + 1) _ step.1
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
    (node : Node α β) (wf : WellFormed (fun k => (hash k).toUSize >>> offset) node)
    (key : α) (value : β) :
    letI res := insertNode levels offset node ((hash key).toUSize >>> offset) key value
    WellFormed (fun k => (hash k).toUSize >>> offset) res ∧
      ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by
  induction levels generalizing offset node key value with
  | zero => exact insertNoExpand_wf_mem wf key value
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
      apply insertEntries_wf_mem _ es _ key value wf
      cases wf <;> grind [Array.mem_iff_getElem]
    | collision keys vals hsz =>
      simp only [insertNode]
      generalize hc : insertCollision keys vals hsz key value = b
      have hm (q : α) : HasKey q b.val ↔ q = key ∨ HasKey q (.collision keys vals hsz) := by
        rw [← hc]
        exact insertCollisionAux_mem keys vals hsz 0 key q value
      obtain ⟨node, hb⟩ := b
      cases hb with
      | mk keys' vals' hsz' =>
        simp only [getCollisionNodeSize]
        split
        · exact ⟨.collision _ _ _ _, hm⟩
        · have rebuilt := rebuild_wf_mem (insertNode levels (offset + shift)) offset childSpec
            keys' vals' hsz' 0 mkEmptyEntriesArray (wellFormed_empty _)
          refine ⟨rebuilt.1, ?_⟩
          intro q
          rw [rebuilt.2]
          simpa [hasKey_entries, mkEmptyEntriesArray, EntryHasKey, ← Array.mem_iff_getElem] using hm q

/-- Rebuilding preserves every binding of a distinct bucket. The accumulator
must not already contain a key in the unprocessed suffix. -/
theorem rebuild_unique_bindings [BEq α] [LawfulBEq α] [Hashable α]
    (childInsert : Node α β → USize → α → β → Node α β) (offset : USize)
    (childWF :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k v,
        letI res := childInsert n (hashAt k) k v
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (childUpd :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → Unique n → ∀ k v,
        letI res := childInsert n (hashAt k) k v
        Unique res ∧ Updated n res k v)
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (distinct : DistinctKeys keys) (i : Nat)
    (es : Array (Entry α β (Node α β)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es)) (hu : Unique (.entries es))
    (disjoint : ∀ (j : Nat) (hj : j < keys.size), i ≤ j → ¬ HasKey keys[j] (.entries es)) :
    letI res := rebuild childInsert offset ⟨.collision keys vals hsz, .mk ..⟩ i es
    Unique (.entries res) ∧
      ∀ q w, HasBinding q w (.entries res) ↔
        HasBinding q w (.entries es) ∨
          ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = q ∧ vals[j]'(hsz ▸ hj) = w := by
  rw [rebuild.eq_def]
  dsimp only
  split
  · rename_i hi
    have stepWM := insertEntries_wf_mem (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i]
      (vals[i]'(hsz ▸ hi)) wf (by
        cases wf <;> grind [Array.mem_iff_getElem])
    have stepUV := insertEntries_unique_updated (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i]
      (vals[i]'(hsz ▸ hi)) wf hu (by
        cases wf <;> grind [Array.mem_iff_getElem])
    have nextDisjoint : ∀ (j : Nat) (hj : j < keys.size), i + 1 ≤ j →
        ¬ HasKey keys[j] (.entries (insertEntries es (fun child _ => childInsert child)
          ((hash keys[i]).toUSize >>> offset) keys[i] (vals[i]'(hsz ▸ hi)))) := by
      intro j hj hij
      rw [stepWM.2]
      grind [DistinctKeys]
    obtain ⟨hu', hb'⟩ := rebuild_unique_bindings childInsert offset childWF childUpd
      keys vals hsz distinct (i + 1) _ stepWM.1 stepUV.1 nextDisjoint
    refine ⟨hu', ?_⟩
    intro q w
    rw [hb', stepUV.2]
    grind [HasBinding.hasKey]
  · exact ⟨hu, by grind⟩
termination_by keys.size - i

theorem insertNode_unique_updated [BEq α] [LawfulBEq α] [Hashable α] (levels : Nat)
    (offset : USize) (bound : offset.toNat + 5 * levels ≤ 30)
    (node : Node α β) (wf : WellFormed (fun k => (hash k).toUSize >>> offset) node)
    (hu : Unique node) (key : α) (value : β) :
    letI res := insertNode levels offset node ((hash key).toUSize >>> offset) key value
    Unique res ∧ Updated node res key value := by
  induction levels generalizing offset node key value with
  | zero => exact insertNoExpand_unique_updated wf hu key value
  | succ levels ih =>
    have hb : offset.toNat + 5 ≤ 30 := by omega
    have hn : (offset + shift).toNat + 5 * levels ≤ 30 := by
      rw [offset_add_shift offset hb]
      omega
    have childWF := insertNode_wf_mem (α := α) (β := β) levels (offset + shift) hn
    have childUpd := ih (offset + shift) hn
    simp only [hash_shift_offset _ offset hb] at childWF childUpd
    cases node with
    | entries es =>
      simp only [insertNode]
      apply insertEntries_unique_updated _ es _ key value wf hu
      cases wf <;> grind [Array.mem_iff_getElem]
    | collision keys vals hsz =>
      have distinct : DistinctKeys keys := by cases hu with | collision h => exact h
      have uv := insertCollisionAux_unique_updated keys vals hsz distinct 0 key value (by omega)
      rw [← insertCollision.eq_def] at uv
      simp only [insertNode]
      generalize hc : insertCollision keys vals hsz key value = b at uv ⊢
      obtain ⟨node, hb⟩ := b
      cases hb with
      | mk keys' vals' hsz' =>
        simp only [getCollisionNodeSize]
        split
        · exact uv
        · have distinct' : DistinctKeys keys' := by cases uv.1 with | collision h => exact h
          have rebuilt := rebuild_unique_bindings (insertNode levels (offset + shift)) offset
            childWF childUpd keys' vals' hsz' distinct' 0 mkEmptyEntriesArray
            (wellFormed_empty _) unique_empty (by
              intro j hj hij
              simp [hasKey_entries, mkEmptyEntriesArray, EntryHasKey])
          refine ⟨rebuilt.1, ?_⟩
          intro q w
          rw [rebuilt.2]
          simpa [hasBinding_entries, mkEmptyEntriesArray, EntryHasBinding] using uv.2 q w

section MainParts

/-- Insertion preserves the routing invariant even when the input has duplicate keys. -/
theorem valid_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) (value : β) :
    Valid (insert map key value) := by
  simpa [Valid, insert] using
    (insertNode_wf_mem (maxDepth.toNat - 1) 0 root_offset_bound map.root
      (by simpa [Valid] using wf) key value).1

/-- Exact membership update; uniqueness is not needed. -/
theorem mem_insert_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key q : α) (value : β) :
    Mem q (insert map key value) ↔ q = key ∨ Mem q map := by
  simpa [Mem, insert] using
    (insertNode_wf_mem (maxDepth.toNat - 1) 0 root_offset_bound map.root
      (by simpa [Valid] using wf) key value).2 q

theorem unique_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) : Unique (insert map key value).root := by
  simpa [insert] using
    (insertNode_unique_updated (maxDepth.toNat - 1) 0 root_offset_bound map.root
      (by simpa [Valid] using wf) hu key value).1

/-- The complete key/value update law. Replacing a key discards its old binding;
all other bindings are preserved. `Unique` rules out duplicate collision keys. -/
theorem mapsTo_insert_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value w : β) :
    MapsTo q w (insert map key value) ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ MapsTo q w map) := by
  simpa [MapsTo, insert] using
    (insertNode_unique_updated (maxDepth.toNat - 1) 0 root_offset_bound map.root
      (by simpa [Valid] using wf) hu key value).2 q w

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

-- FIXME: Remove this after bumping to later versions of Lean
/-- Duplicate-free lists with the same elements have the same length. -/
private theorem length_eq_of_nodup_of_mem_iff [BEq α] [LawfulBEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁.length = l₂.length :=
  (List.perm_iff_count.mpr fun a => by simp only [h₁.count, h₂.count, h a]).length_eq

/-- Insertion adds one key exactly when the key is new. -/
theorem keyCount_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) :
    keyCount (insert map key value).root =
      if contains map key then keyCount map.root else keyCount map.root + 1 := by
  have wf' := valid_insert map wf key value
  have hnodup := nodup_keyList wf hu
  have hnodup' := nodup_keyList wf' (unique_insert map wf hu key value)
  have hmem : ∀ q, q ∈ keyList (insert map key value).root ↔ q = key ∨ q ∈ keyList map.root := by
    intro q
    rw [mem_keyList wf' q, mem_keyList wf q]
    exact mem_insert_iff map wf key q value
  unfold keyCount
  split
  · rename_i hc
    have hk : key ∈ keyList map.root :=
      (mem_keyList wf key).mpr ((contains_eq_true_iff map wf key).mp hc)
    apply length_eq_of_nodup_of_mem_iff hnodup' hnodup
    intro q
    rw [hmem]
    constructor
    · rintro (rfl | h) <;> assumption
    · exact Or.inr
  · rename_i hc
    have hk : key ∉ keyList map.root := fun h =>
      hc ((contains_eq_true_iff map wf key).mpr ((mem_keyList wf key).mp h))
    rw [← List.length_cons]
    apply length_eq_of_nodup_of_mem_iff hnodup' (List.nodup_cons.mpr ⟨hk, hnodup⟩)
    intro q
    rw [hmem, List.mem_cons]

end MainParts

end VerifiedHAMT
