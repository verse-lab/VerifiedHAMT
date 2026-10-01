import HAMTVerify.Insert
/-! Kernel-checked equivalence between the cached-hash insertion and our
original total algorithm. This does not assert equality with upstream partial
constants. The offset bound handles both 32-bit and 64-bit USize semantics. -/

namespace HAMTVerify
open Lean.PersistentHashMap

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

variable {α : Type u} {β : Type v}

theorem insertCollision_eq [BEq α] (b : Bucket α β) (i : Nat) (key : α) (value : β) :
    insertCollision ⟨.collision b.keys b.vals b.size_eq, .mk ..⟩ i key value =
      ⟨(insertAt b i key value).node, .mk ..⟩ := by
  apply Subtype.ext
  cases b with
  | mk keys vals hsz =>
    dsimp only [Bucket.node]
    rw [insertCollision, insertAt]
    split
    · split
      · rfl
      · exact congrArg Subtype.val (insertCollision_eq ⟨keys, vals, hsz⟩ (i + 1) key value)
    · rfl
termination_by b.keys.size - i

theorem insertEntriesCached_eq [BEq α]
    (cached : Node α β → USize → α → β → Node α β)
    (child : Node α β → α → β → Node α β) (hashAt : α → USize)
    (agree : ∀ n k v, cached n (nextHash (hashAt k)) k v = child n k v)
    (es : Array (Entry α β (Node α β))) (key : α) (value : β) :
    insertEntriesCached cached es (hashAt key) key value =
      insertEntries child hashAt es key value := by
  unfold insertEntriesCached insertEntries
  congr 1
  funext entry
  cases entry <;> simp only [agree]

theorem rebuildCached_eq [BEq α] [Hashable α]
    (cached : Node α β → USize → α → β → Node α β)
    (child : Node α β → α → β → Node α β) (offset : USize)
    (agree : ∀ n k v, cached n (nextHash ((hash k).toUSize >>> offset)) k v = child n k v)
    (b : Bucket α β) (i : Nat) (es : Array (Entry α β (Node α β))) :
    rebuildCached cached offset b i es =
      rebuild child (fun k => (hash k).toUSize >>> offset) b i es := by
  rw [rebuildCached, rebuild]
  split
  · dsimp only
    rw [insertEntriesCached_eq cached child _ agree]
    exact rebuildCached_eq cached child offset agree b (i + 1) _
  · rfl
termination_by b.keys.size - i

theorem offset_add_shift (offset : USize) (bound : offset.toNat + 5 ≤ 30) :
    (offset + shift).toNat = offset.toNat + 5 := by
  change (offset + 5).toNat = offset.toNat + 5
  rcases System.Platform.numBits_eq with hb | hb <;>
    simp only [USize.toNat_add, USize.toNat_ofNat, hb, Nat.reducePow, Nat.reduceMod] <;>
    exact Nat.mod_eq_of_lt (by omega)

/-- Equality of two total algorithms, with no routing or uniqueness premise. -/
theorem insertNodeCached_eq [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (bound : offset.toNat + 5 * levels ≤ 30) (node : Node α β) (key : α) (value : β) :
    insertNodeCached levels offset node ((hash key).toUSize >>> offset) key value =
      insertNode levels (fun k => (hash k).toUSize >>> offset) node key value := by
  induction levels generalizing offset node key value with
  | zero => rfl
  | succ levels ih =>
    have hb : offset.toNat + 5 ≤ 30 := by omega
    have hn : (offset + shift).toNat + 5 * levels ≤ 30 := by
      rw [offset_add_shift offset hb]
      omega
    have agree : ∀ (n : Node α β) k v,
        insertNodeCached levels (offset + shift) n
          (nextHash ((hash k).toUSize >>> offset)) k v =
        insertNode levels (fun q => nextHash ((hash q).toUSize >>> offset)) n k v := by
      intro n k v
      simpa only [hash_shift_offset _ offset hb] using ih (offset + shift) hn n k v
    cases node with
    | entries es =>
      simp only [insertNodeCached, insertNode]
      rw [insertEntriesCached_eq _ _ _ agree]
    | collision keys vals hsz =>
      simp only [insertNodeCached, insertNode]
      rw [insertCollision_eq ⟨keys, vals, hsz⟩]
      simp only [Bucket.node]
      split
      · rfl
      · rw [rebuildCached_eq _ _ _ agree]

theorem insert_root_eq [BEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (key : α) (value : β) :
    (insert map key value).root =
      insertNode (maxDepth.toNat - 1) (fun k => (hash k).toUSize) map.root key value := by
  have bound : (0 : USize).toNat + 5 * (maxDepth.toNat - 1) ≤ 30 := by
    rcases System.Platform.numBits_eq with hb | hb <;>
      simp [maxDepth, USize.toNat_ofNat, hb]
  simpa [insert] using insertNodeCached_eq (maxDepth.toNat - 1) 0 bound map.root key value
end HAMTVerify
