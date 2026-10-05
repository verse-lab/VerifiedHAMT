module

public import HAMTVerify.Basic
public import Init.Data.Array.Basic

@[expose] public section

namespace HAMTVerify

open Lean.PersistentHashMap (shift maxDepth)

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

theorem root_offset_bound : (0 : USize).toNat + 5 * (maxDepth.toNat - 1) ≤ 30 := by
  rcases System.Platform.numBits_eq with hb | hb <;>
    simp [maxDepth, USize.toNat_ofNat, hb]

end HAMTVerify
