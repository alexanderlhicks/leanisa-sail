/-
Carryless multiplication refinement for the actual extracted Sail operation.
The bit decomposition and arbitrary-state loop invariant are proved here
against the generated operation.
-/
import QuotientRepresentation

noncomputable section
open Polynomial
namespace Leanisa.Proofs.Quotient


theorem bitsPoly_right_decomposition (y : BitVec 64) :
    bitsPoly y = C (bitCoeff (y.getLsbD 0)) + bitsPoly (y >>> (1 : Nat)) * X := by
  ext i
  cases i with
  | zero => simp [bitsPoly_coeff]
  | succ j =>
    simp only [coeff_add, coeff_mul_X, coeff_C, Nat.add_one_ne_zero, ↓reduceIte,
      zero_add, bitsPoly_coeff, BitVec.getLsbD_ushiftRight]
    by_cases hj : j < 64
    · by_cases hj1 : j + 1 < 64
      · simp [hj, hj1, Nat.add_comm]
      · have hge : 64 ≤ 1 + j := by omega
        simp [hj, hj1, BitVec.getLsbD_of_ge _ _ hge, bitCoeff]
    · have hj1 : ¬ j + 1 < 64 := by omega
      simp [hj, hj1]

theorem toK_right_decomposition (y : BitVec 64) :
    toK y = (if y.getLsbD 0 then 1 else 0) +
      toK (y >>> (1 : Nat)) * AdjoinRoot.root modulus := by
  have h := congrArg (AdjoinRoot.mk modulus) (bitsPoly_right_decomposition y)
  simp only [map_add, map_mul, AdjoinRoot.mk_X] at h
  have hc : AdjoinRoot.mk modulus (C (bitCoeff (y.getLsbD 0))) =
      (if y.getLsbD 0 then 1 else 0) := by
    cases y.getLsbD 0 <;> simp [bitCoeff]
  rw [hc] at h
  exact h

theorem multiplier_projection (n : Nat) (s : MulState) :
    (mulIter n s).multiplier = s.multiplier >>> n := by
  induction n generalizing s with
  | zero => simp [mulIter]
  | succ n ih =>
    rw [mulIter, ih]
    simp only [mulStep]
    rw [← BitVec.shiftRight_add]
    simp [Nat.add_comm]

theorem multiplier_terminal (s : MulState) :
    (mulIter 64 s).multiplier = 0 := by
  rw [multiplier_projection, BitVec.ushiftRight_eq_zero (by decide)]
  rfl

def mulInvariant (s : MulState) : KRing :=
  toK s.accumulator + toK s.multiplicand * toK s.multiplier

theorem mulInvariant_step (s : MulState) : mulInvariant (mulStep s) = mulInvariant s := by
  rcases s with ⟨x, y, z⟩
  change toK (if y.getLsbD 0 then z ^^^ x else z) +
    toK (xtime x) * toK (y >>> (1 : Nat)) = toK z + toK x * toK y
  rw [toK_xtime, toK_right_decomposition y]
  cases hbit : y.getLsbD 0
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    ac_rfl
  · simp only [↓reduceIte, toK_xor, mul_add, mul_one]
    ac_rfl

/-- Every structural step preserves the invariant for an arbitrary supplied state. -/
theorem mulInvariant_iter (n : Nat) (s : MulState) :
    mulInvariant (mulIter n s) = mulInvariant s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [mulIter, ih, mulInvariant_step]

/-- Full-width reference-loop endpoint, including an arbitrary initial accumulator.
This is a reference-state theorem, not an extracted hidden-register assertion. -/
theorem mulIter_accumulator (s : MulState) :
    toK (mulIter 64 s).accumulator =
      toK s.accumulator + toK s.multiplicand * toK s.multiplier := by
  have h := mulInvariant_iter 64 s
  unfold mulInvariant at h
  rw [multiplier_terminal] at h
  change toK (mulIter 64 s).accumulator +
    toK (mulIter 64 s).multiplicand * toK (0#64) = _ at h
  rw [toK_zero, mul_zero, add_zero] at h
  exact h

theorem toK_mulRef (a b : BitVec 64) : toK (mulRef a b) = toK a * toK b := by
  have h := mulIter_accumulator ⟨a, b, 0⟩
  change toK (mulRef a b) = toK (0#64) + toK a * toK b at h
  rw [toK_zero, zero_add] at h
  exact h

/-- The actual extracted Sail multiplication is carryless multiplication in the
fixed quotient ring, unconditionally for every pair of 64-bit words. -/
theorem toK_kmul (a b : BitVec 64) :
    toK (Leanisa.Functions.kmul a b) = toK a * toK b := by
  rw [sail_kmul_eq_mulRef, toK_mulRef]

/-- The arbitrary-accumulator endpoint also reflects back to word equality. -/
theorem mulIter_accumulator_eq (s : MulState) :
    (mulIter 64 s).accumulator =
      s.accumulator ^^^ Leanisa.Functions.kmul s.multiplicand s.multiplier := by
  apply toK_injective
  rw [mulIter_accumulator, toK_xor, toK_kmul]

theorem kmul_zero_right (a : BitVec 64) : Leanisa.Functions.kmul a (0#64) = 0#64 := by
  apply toK_injective
  rw [toK_kmul, toK_zero, mul_zero]

theorem kmul_zero_left (a : BitVec 64) : Leanisa.Functions.kmul (0#64) a = 0#64 := by
  apply toK_injective
  rw [toK_kmul, toK_zero, zero_mul]

theorem kmul_one_right (a : BitVec 64) : Leanisa.Functions.kmul a (1#64) = a := by
  apply toK_injective
  rw [toK_kmul, toK_one, mul_one]

theorem kmul_one_left (a : BitVec 64) : Leanisa.Functions.kmul (1#64) a = a := by
  apply toK_injective
  rw [toK_kmul, toK_one, one_mul]

theorem kmul_comm (a b : BitVec 64) :
    Leanisa.Functions.kmul a b = Leanisa.Functions.kmul b a := by
  apply toK_injective
  simp only [toK_kmul, mul_comm]

theorem kmul_assoc (a b c : BitVec 64) :
    Leanisa.Functions.kmul (Leanisa.Functions.kmul a b) c =
      Leanisa.Functions.kmul a (Leanisa.Functions.kmul b c) := by
  apply toK_injective
  simp only [toK_kmul, mul_assoc]

theorem kmul_xor_right (a b c : BitVec 64) :
    Leanisa.Functions.kmul a (b ^^^ c) =
      Leanisa.Functions.kmul a b ^^^ Leanisa.Functions.kmul a c := by
  apply toK_injective
  simp only [toK_kmul, toK_xor, mul_add]

theorem kmul_xor_left (a b c : BitVec 64) :
    Leanisa.Functions.kmul (a ^^^ b) c =
      Leanisa.Functions.kmul a c ^^^ Leanisa.Functions.kmul b c := by
  apply toK_injective
  simp only [toK_kmul, toK_xor, add_mul]

end Leanisa.Proofs.Quotient
