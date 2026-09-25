import QuotientRepresentation

open Polynomial Leanisa.Proofs.Quotient
noncomputable section
namespace Leanisa.Proofs.QuotientChecks

theorem coefficient_zero : (bitsPoly (1#64)).coeff 0 = 1 := by
  rw [bitsPoly_coeff]; decide

theorem coefficient_63 : (bitsPoly (0x8000000000000000#64)).coeff 63 = 1 := by
  rw [bitsPoly_coeff]; decide

theorem coefficient_64 (a : BitVec 64) : (bitsPoly a).coeff 64 = 0 := by
  simp only [bitsPoly_coeff, lt_self_iff_false, ↓reduceIte]

theorem coefficient_beyond (a : BitVec 64) (i : Nat) (hi : 64 ≤ i) :
    (bitsPoly a).coeff i = 0 := by
  rw [bitsPoly_coeff, if_neg (by omega)]

theorem xtime_zero : xtime (0#64) = 0#64 := by decide

theorem xtime_one : xtime (1#64) = 2#64 := by decide

theorem xtime_high_carry : xtime (0x8000000000000000#64) = 0x1b#64 := by decide

theorem every_bit_xtime : ∀ i : Fin 64,
    xtime ((1#64) <<< i.val) =
      if i.val < 63 then (1#64) <<< (i.val + 1) else 0x1b#64 := by decide

theorem every_bit_polynomial (i : Fin 64) :
    bitsPoly ((1#64) <<< i.val) = (X : Polynomial (ZMod 2)) ^ (i.val) := by
  ext j
  rw [bitsPoly_coeff, coeff_X_pow, BitVec.getLsbD_shiftLeft]
  by_cases hj : j < 64
  · by_cases heq : j = i.val
    · subst j
      simp [i.isLt, bitCoeff]
    · by_cases hij : j < i.val
      · simp [hj, hij, bitCoeff, heq]
      · have hdiff : j - i.val ≠ 0 := by omega
        simp [hj, hij, hdiff, bitCoeff, heq]
  · have hne : j ≠ i.val := by omega
    simp [hj, hne]

theorem every_bit_quotient (i : Fin 64) :
    toK ((1#64) <<< i.val) = AdjoinRoot.root modulus ^ i.val := by
  simp only [toK, every_bit_polynomial, map_pow, AdjoinRoot.mk_X]

theorem xtime_high_carry_image :
    toK (xtime (0x8000000000000000#64)) = AdjoinRoot.root modulus ^ 64 := by
  rw [xtime_high_carry, toK_reduction_literal, root_reduction]

theorem word_two_nonzero : toK (2#64) ≠ 0 := by
  rw [← toK_zero]
  intro h
  have := toK_injective h
  contradiction

theorem ring_two_zero : (2 : KRing) = 0 := by
  simpa only [one_add_one_eq_two] using ZModModule.add_self (1 : KRing)

end Leanisa.Proofs.QuotientChecks
