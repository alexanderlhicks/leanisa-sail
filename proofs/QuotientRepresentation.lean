/-
Quotient-ring representation of 64-bit words for the ISA polynomial.
This module proves the representation, degree, and injectivity facts used
to interpret the generated Sail field operations.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot
import FieldLoops

noncomputable section
open Polynomial
namespace Leanisa.Proofs.Quotient

def bitCoeff (b : Bool) : ZMod 2 := if b then 1 else 0

def bitsPoly (a : BitVec 64) : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range 64, monomial i (bitCoeff (a.getLsbD i))

theorem bitsPoly_coeff (a : BitVec 64) (i : Nat) :
    (bitsPoly a).coeff i = if i < 64 then bitCoeff (a.getLsbD i) else 0 := by
  simp [bitsPoly, finset_sum_coeff, coeff_monomial]

theorem bitsPoly_degree_lt (a : BitVec 64) : (bitsPoly a).degree < 64 := by
  apply (degree_lt_iff_coeff_zero _ 64).mpr
  intro i hi
  rw [bitsPoly_coeff, if_neg (by omega)]

theorem bitsPoly_injective : Function.Injective bitsPoly := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hcoeff := congrArg (fun p : Polynomial (ZMod 2) => p.coeff i) h
  simp only [bitsPoly_coeff, if_pos hi] at hcoeff
  cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;>
    simp_all [bitCoeff]

def low : Polynomial (ZMod 2) := X^4 + X^3 + X + 1
def modulus : Polynomial (ZMod 2) := X^64 + low

theorem low_degree_lt : low.degree < 64 := by
  apply (degree_lt_iff_coeff_zero _ 64).mpr
  intro i hi
  have h4 : i ≠ 4 := by omega
  have h3 : i ≠ 3 := by omega
  have h1 : 1 ≠ i := by omega
  have h0 : i ≠ 0 := by omega
  simp [low, coeff_add, coeff_X_pow, coeff_X, coeff_one, h4, h3, h1, h0]

theorem modulus_monic : modulus.Monic := monic_X_pow_add low_degree_lt

theorem modulus_degree : modulus.degree = 64 := by
  have h : low.degree < (X^64 : Polynomial (ZMod 2)).degree := by
    simpa only [degree_X_pow] using low_degree_lt
  simpa only [modulus, degree_X_pow] using degree_add_eq_left_of_degree_lt h

theorem modulus_natDegree : modulus.natDegree = 64 := by
  have h : modulus.degree = (X^64 : Polynomial (ZMod 2)).degree := by
    simpa only [degree_X_pow] using modulus_degree
  simpa only [natDegree_X_pow] using natDegree_eq_of_degree_eq h

abbrev KRing := AdjoinRoot modulus
def toK (a : BitVec 64) : KRing := AdjoinRoot.mk modulus (bitsPoly a)

theorem bitCoeff_xor (a b : Bool) : bitCoeff (a ^^ b) = bitCoeff a + bitCoeff b := by
  cases a <;> cases b <;> decide

theorem bitsPoly_xor (a b : BitVec 64) : bitsPoly (a ^^^ b) = bitsPoly a + bitsPoly b := by
  ext i
  by_cases h : i < 64
  · simp [bitsPoly_coeff, h, bitCoeff_xor]
  · simp [bitsPoly_coeff, h]

theorem toK_xor (a b : BitVec 64) : toK (a ^^^ b) = toK a + toK b := by
  simp only [toK, bitsPoly_xor, map_add]

theorem toK_injective : Function.Injective toK := by
  intro a b h
  apply bitsPoly_injective
  by_contra hne
  have hnz : bitsPoly a - bitsPoly b ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (bitsPoly a - bitsPoly b).degree < modulus.degree := by
    rw [modulus_degree]
    exact (degree_sub_le _ _).trans_lt (max_lt (bitsPoly_degree_lt a) (bitsPoly_degree_lt b))
  exact (modulus_monic.not_dvd_of_degree_lt hnz hdeg) (AdjoinRoot.mk_eq_mk.mp h)

/-- The shift discards precisely the old coefficient of X^63. -/
theorem bitsPoly_shiftLeft (a : BitVec 64) :
    bitsPoly (a <<< (1 : Nat)) + C (bitCoeff (a.getLsbD 63)) * X^64 =
      bitsPoly a * X := by
  ext i
  cases i with
  | zero =>
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_mul_X_zero, bitsPoly_coeff]
    simp [bitCoeff]
  | succ j =>
    rw [coeff_add, coeff_C_mul, coeff_X_pow, coeff_mul_X, bitsPoly_coeff,
      bitsPoly_coeff, BitVec.getLsbD_shiftLeft]
    by_cases h : j + 1 < 64
    · have hj : j < 64 := by omega
      have hn : j + 1 ≠ 64 := by omega
      simp [h, hj, hn]
    · by_cases heq : j + 1 = 64
      · have hj : j = 63 := by omega
        subst j
        simp
      · have hj : ¬ j < 64 := by omega
        simp [h, hj, heq]

theorem bitsPoly_zero : bitsPoly (0#64) = 0 := by
  ext i
  simp [bitsPoly_coeff, bitCoeff]

theorem bitsPoly_one : bitsPoly (1#64) = 1 := by
  ext i
  cases i with
  | zero => simp [bitsPoly_coeff, bitCoeff]
  | succ j => simp [bitsPoly_coeff, bitCoeff, coeff_one]

theorem bitsPoly_two : bitsPoly (2#64) = X := by
  have ht : ∀ i : Fin 64, (2#64).getLsbD i = decide (i.val = 1) := by decide
  ext i
  by_cases hi : i < 64
  · have h := ht ⟨i, hi⟩
    by_cases h1 : i = 1
    · subst i; simp [bitsPoly_coeff, bitCoeff]
    · have h1' : 1 ≠ i := Ne.symm h1
      rw [bitsPoly_coeff, if_pos hi, h]
      simp [bitCoeff, coeff_X, h1, h1']
  · have h1 : 1 ≠ i := by omega
    simp [bitsPoly_coeff, hi, coeff_X, h1]

theorem bitsPoly_reduction_literal : bitsPoly (0x1b#64) = low := by
  have ht : ∀ i : Fin 64, bitCoeff ((0x1b#64).getLsbD i) =
      (if i.val = 4 then 1 else 0) + (if i.val = 3 then 1 else 0) +
      (if i.val = 1 then 1 else 0) + (if i.val = 0 then 1 else 0) := by decide
  ext i
  by_cases hi : i < 64
  · simpa [bitsPoly_coeff, hi, low, coeff_add, coeff_X_pow, coeff_X, coeff_one,
      eq_comm] using ht ⟨i, hi⟩
  · have h4 : i ≠ 4 := by omega
    have h3 : i ≠ 3 := by omega
    have h1 : 1 ≠ i := by omega
    have h0 : i ≠ 0 := by omega
    simp [bitsPoly_coeff, hi, low, coeff_add, coeff_X_pow, coeff_X, coeff_one,
      h4, h3, h1, h0]

theorem toK_zero : toK (0#64) = 0 := by simp only [toK, bitsPoly_zero, map_zero]
theorem toK_one : toK (1#64) = 1 := by simp only [toK, bitsPoly_one, map_one]
/-- The bitvector word 2 represents X; the ring numeral 2 is a separate notion. -/
theorem toK_two : toK (2#64) = AdjoinRoot.root modulus := by
  simp only [toK, bitsPoly_two, AdjoinRoot.mk_X]
theorem toK_reduction_literal : toK (0x1b#64) =
    AdjoinRoot.root modulus ^ 4 + AdjoinRoot.root modulus ^ 3 +
      AdjoinRoot.root modulus + 1 := by
  simp only [toK, bitsPoly_reduction_literal, low, map_add, map_pow, map_one,
    AdjoinRoot.mk_X]

theorem root_modulus_relation :
    AdjoinRoot.root modulus ^ 64 +
      (AdjoinRoot.root modulus ^ 4 + AdjoinRoot.root modulus ^ 3 +
        AdjoinRoot.root modulus + 1) = 0 := by
  have h := AdjoinRoot.mk_self (f := modulus)
  change AdjoinRoot.mk modulus (X ^ 64 + (X ^ 4 + X ^ 3 + X + 1)) = 0 at h
  simpa only [map_add, map_pow, map_one, AdjoinRoot.mk_X] using h

theorem root_reduction :
    AdjoinRoot.root modulus ^ 64 =
      AdjoinRoot.root modulus ^ 4 + AdjoinRoot.root modulus ^ 3 +
        AdjoinRoot.root modulus + 1 := by
  have h := eq_neg_of_add_eq_zero_left root_modulus_relation
  simpa only [ZModModule.neg_eq_self] using h

theorem toK_xtime (a : BitVec 64) :
    toK (Leanisa.Proofs.xtime a) = toK a * AdjoinRoot.root modulus := by
  have h := congrArg (AdjoinRoot.mk modulus) (bitsPoly_shiftLeft a)
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X] at h
  rw [Leanisa.Proofs.xtime, toK_xor]
  cases hc : a.getLsbD 63
  · change toK (a <<< (1 : Nat)) + toK (0#64) = _
    rw [toK_zero, add_zero]
    rw [hc] at h
    change toK (a <<< (1 : Nat)) + AdjoinRoot.mk modulus (C 0) *
      AdjoinRoot.root modulus ^ 64 = _ at h
    rw [C_0, map_zero, zero_mul, add_zero] at h
    exact h
  · change toK (a <<< (1 : Nat)) + toK (0x1b#64) = _
    rw [toK_reduction_literal]
    rw [hc] at h
    change toK (a <<< (1 : Nat)) + AdjoinRoot.mk modulus (C 1) *
      AdjoinRoot.root modulus ^ 64 = _ at h
    rw [C_1, map_one, one_mul, root_reduction] at h
    exact h

/-- The actual extracted Sail advance has the same quotient-ring meaning. -/
theorem toK_sail_advance (a : BitVec 64) :
    toK (Leanisa.Functions.advance a) = toK a * AdjoinRoot.root modulus := by
  rw [Leanisa.Proofs.sail_advance_eq_xtime, toK_xtime]

end Leanisa.Proofs.Quotient
