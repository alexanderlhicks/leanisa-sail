import QuotientRepresentationChecks

open Polynomial Leanisa.Proofs.Quotient Leanisa.Proofs.QuotientChecks
noncomputable section
namespace Leanisa.Proofs.WrongPolynomialWitness

/-- Mutation: remove only the constant term from the quotient modulus.
The accepted `Leanisa.Proofs.xtime`, with reduction word 0x1b, is unchanged. -/
def wrongLow : Polynomial (ZMod 2) := X^4 + X^3 + X

def wrongModulus : Polynomial (ZMod 2) := X^64 + wrongLow

def wrongToK (a : BitVec 64) : AdjoinRoot wrongModulus :=
  AdjoinRoot.mk wrongModulus (bitsPoly a)

theorem wrongLow_degree_lt : wrongLow.degree < 64 := by
  apply (degree_lt_iff_coeff_zero _ 64).mpr
  intro i hi
  have h4 : i ≠ 4 := by omega
  have h3 : i ≠ 3 := by omega
  have h1 : 1 ≠ i := by omega
  simp [wrongLow, coeff_add, coeff_X_pow, coeff_X, h4, h3, h1]

theorem wrongModulus_monic : wrongModulus.Monic :=
  monic_X_pow_add wrongLow_degree_lt

theorem wrongModulus_degree : wrongModulus.degree = 64 := by
  have h : wrongLow.degree < (X^64 : Polynomial (ZMod 2)).degree := by
    simpa only [degree_X_pow] using wrongLow_degree_lt
  simpa only [wrongModulus, degree_X_pow] using degree_add_eq_left_of_degree_lt h

theorem wrongToK_injective : Function.Injective wrongToK := by
  intro a b h
  apply bitsPoly_injective
  by_contra hne
  have hnz : bitsPoly a - bitsPoly b ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (bitsPoly a - bitsPoly b).degree < wrongModulus.degree := by
    rw [wrongModulus_degree]
    exact (degree_sub_le _ _).trans_lt (max_lt (bitsPoly_degree_lt a) (bitsPoly_degree_lt b))
  exact (wrongModulus_monic.not_dvd_of_degree_lt hnz hdeg) (AdjoinRoot.mk_eq_mk.mp h)

theorem wrongRoot_reduction :
    AdjoinRoot.root wrongModulus ^ 64 =
      AdjoinRoot.root wrongModulus ^ 4 + AdjoinRoot.root wrongModulus ^ 3 +
        AdjoinRoot.root wrongModulus := by
  have h := AdjoinRoot.mk_self (f := wrongModulus)
  change AdjoinRoot.mk wrongModulus (X ^ 64 + (X ^ 4 + X ^ 3 + X)) = 0 at h
  simp only [map_add, map_pow, AdjoinRoot.mk_X] at h
  simpa only [ZModModule.neg_eq_self] using eq_neg_of_add_eq_zero_left h

theorem wrongLiteral_polynomial : bitsPoly (0x1a#64) = wrongLow := by
  rw [show (0x1a#64) = (0x1b#64) ^^^ (1#64) by decide, bitsPoly_xor,
    bitsPoly_reduction_literal, bitsPoly_one]
  change (wrongLow + 1) + 1 = wrongLow
  rw [add_assoc, ZModModule.add_self, add_zero]

theorem wrongLiteral_image : wrongToK (0x1a#64) = AdjoinRoot.root wrongModulus ^ 64 := by
  rw [wrongToK, wrongLiteral_polynomial, wrongLow]
  simp only [map_add, map_pow, AdjoinRoot.mk_X, wrongRoot_reduction]

theorem wrong_high_carry_shift :
    wrongToK (0x8000000000000000#64) * AdjoinRoot.root wrongModulus =
      AdjoinRoot.root wrongModulus ^ 64 := by
  have h := congrArg (AdjoinRoot.mk wrongModulus)
    (bitsPoly_shiftLeft (0x8000000000000000#64))
  rw [show ((0x8000000000000000#64) <<< (1 : Nat)) = 0#64 by decide,
    bitsPoly_zero] at h
  change AdjoinRoot.mk wrongModulus (0 + C 1 * X ^ 64) =
    AdjoinRoot.mk wrongModulus (bitsPoly (0x8000000000000000#64) * X) at h
  simpa only [C_1, one_mul, zero_add, map_pow, map_mul, AdjoinRoot.mk_X,
    wrongToK] using h.symm

/-- A concrete logical refutation of the incorrect xtime correspondence. -/
theorem high_carry_refutes_wrong_polynomial :
    wrongToK (xtime (0x8000000000000000#64)) ≠
      wrongToK (0x8000000000000000#64) * AdjoinRoot.root wrongModulus := by
  rw [xtime_high_carry, wrong_high_carry_shift, ← wrongLiteral_image]
  intro h
  have hwords := wrongToK_injective h
  have hne : (0x1b#64) ≠ (0x1a#64) := by decide
  exact hne hwords

theorem no_universal_wrong_correspondence :
    ¬ (∀ a : BitVec 64, wrongToK (xtime a) =
      wrongToK a * AdjoinRoot.root wrongModulus) := by
  intro h
  exact high_carry_refutes_wrong_polynomial (h (0x8000000000000000#64))

end Leanisa.Proofs.WrongPolynomialWitness
