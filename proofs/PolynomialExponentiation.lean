/-
Ring-power refinement for the actual extracted Sail exponentiator and bounded
natural address indices. The arbitrary-state loop invariant is proved here
against the generated operation.
-/
import PolynomialMultiplication
import PowerLoops
import Lookup

noncomputable section
namespace Leanisa.Proofs.Quotient

theorem exponent_decomposition (y : BitVec 64) :
    y.toNat = (if y.getLsbD 0 then 1 else 0) +
      2 * (y >>> (1 : Nat)).toNat := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [pow_one, BitVec.getLsbD, Nat.testBit_zero]
  have h := Nat.div_add_mod y.toNat 2
  have hm := Nat.mod_two_eq_zero_or_one y.toNat
  split <;> simp_all
  omega

theorem exponent_projection (n : Nat) (s : PowState) :
    (powIter n s).exponent = s.exponent >>> n := by
  induction n generalizing s with
  | zero => simp [powIter]
  | succ n ih =>
    rw [powIter, ih]
    simp only [powStep]
    rw [← BitVec.shiftRight_add]
    simp [Nat.add_comm]

theorem exponent_terminal (s : PowState) :
    (powIter 64 s).exponent = 0 := by
  rw [exponent_projection, BitVec.ushiftRight_eq_zero (by decide)]
  rfl

def powInvariant (s : PowState) : KRing :=
  toK s.accumulator * (toK s.base) ^ s.exponent.toNat

theorem powInvariant_step (s : PowState) : powInvariant (powStep s) = powInvariant s := by
  rcases s with ⟨x,y,z⟩
  change toK (if y.getLsbD 0 then mulRef z x else z) *
      (toK (mulRef x x)) ^ (y >>> (1 : Nat)).toNat =
    toK z * toK x ^ y.toNat
  rw [toK_mulRef]
  conv_rhs => rw [exponent_decomposition y]
  cases hbit : y.getLsbD 0
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [pow_mul, pow_two]
  · simp only [↓reduceIte, toK_mulRef]
    rw [pow_add, pow_one, pow_mul, pow_two]
    exact mul_assoc _ _ _

theorem encoded_index (i : Nat) (bound : i < 2^64) :
    (BitVec.ofNat 64 i).toNat = i := by
  exact Nat.mod_eq_of_lt bound

theorem encoded_sum_operands (i j : Nat) (bound : i+j < 2^64) :
    (BitVec.ofNat 64 i).toNat = i ∧
    (BitVec.ofNat 64 j).toNat = j ∧
    (BitVec.ofNat 64 (i+j)).toNat = i+j := by
  exact ⟨encoded_index i (by omega), encoded_index j (by omega), encoded_index _ bound⟩

/-- Every number of exact reference steps preserves the arbitrary-state invariant. -/
theorem powInvariant_iter (n : Nat) (s : PowState) :
    powInvariant (powIter n s) = powInvariant s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [powIter, ih, powInvariant_step]

/-- Full-width reference-state endpoint with an arbitrary initial accumulator.
This does not assert extracted hidden-register correspondence. -/
theorem powIter_accumulator (s : PowState) :
    toK (powIter 64 s).accumulator =
      toK s.accumulator * (toK s.base) ^ s.exponent.toNat := by
  have h := powInvariant_iter 64 s
  unfold powInvariant at h
  rw [exponent_terminal] at h
  change toK (powIter 64 s).accumulator * (toK (powIter 64 s).base) ^ 0 = _ at h
  rw [pow_zero, mul_one] at h
  exact h

theorem toK_powRef (n : BitVec 64) :
    toK (powRef n) = (AdjoinRoot.root modulus) ^ n.toNat := by
  have h := powIter_accumulator ⟨2, n, 1⟩
  change toK (powRef n) = toK (1#64) * (toK (2#64)) ^ n.toNat at h
  rw [toK_one, toK_two, one_mul] at h
  exact h

/-- Unconditional ring-power interpretation of the actual extracted gpow. -/
theorem toK_gpow (n : BitVec 64) :
    toK (Leanisa.Functions.gpow n) = (AdjoinRoot.root modulus) ^ n.toNat := by
  rw [sail_gpow_eq_powRef, toK_powRef]

/-- Exact natural-index image, including the existing 64-bit encoding truncation. -/
theorem toK_gAddress_mod (i : Nat) :
    toK (Leanisa.Proofs.gAddress i) = (AdjoinRoot.root modulus) ^ (i % 2^64) := by
  rw [gAddress, toK_gpow]
  rfl

/-- Below the encoding boundary, the address image has the original natural exponent. -/
theorem toK_gAddress (i : Nat) (bound : i < 2^64) :
    toK (Leanisa.Proofs.gAddress i) = (AdjoinRoot.root modulus) ^ i := by
  rw [toK_gAddress_mod, Nat.mod_eq_of_lt bound]

theorem gAddress_origin : Leanisa.Proofs.gAddress 0 = 1#64 := by
  exact sail_gpow_zero

theorem gAddress_one : Leanisa.Proofs.gAddress 1 = 2#64 := by
  apply toK_injective
  rw [toK_gAddress 1 (by decide), toK_two, pow_one]

theorem gAddress_successor (i : Nat) (bound : i + 1 < 2^64) :
    Leanisa.Proofs.gAddress (i + 1) =
      Leanisa.Functions.advance (Leanisa.Proofs.gAddress i) := by
  apply toK_injective
  rw [toK_gAddress _ bound, toK_sail_advance, toK_gAddress i (by omega), pow_succ]

theorem gAddress_add (i j : Nat) (bound : i + j < 2^64) :
    Leanisa.Functions.kmul (Leanisa.Proofs.gAddress i) (Leanisa.Proofs.gAddress j) =
      Leanisa.Proofs.gAddress (i + j) := by
  apply toK_injective
  rw [toK_kmul, toK_gAddress i (by omega), toK_gAddress j (by omega),
    toK_gAddress (i + j) bound, pow_add]

end Leanisa.Proofs.Quotient
