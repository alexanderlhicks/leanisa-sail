/- Directed reference and actual-result checks. The accepted all-ones certificate
is reused explicitly; no large closed exponentiation is recomputed here. -/
import PolynomialExponentiation
import PowerCertificates
import PowerLoopChecks

noncomputable section
open Leanisa.Proofs.Quotient
namespace Leanisa.Proofs.PolynomialExponentiationChecks

theorem zero_steps (s : PowState) : powIter 0 s = s := rfl

set_option maxRecDepth 10000 in
theorem old_base_low_bit : powStep ⟨2, 1, 3⟩ = ⟨4, 0, 6⟩ := by decide

set_option maxRecDepth 10000 in
theorem even_exponent_old_accumulator : powStep ⟨2, 2, 3⟩ = ⟨4, 1, 3⟩ := by decide

theorem high_bit_after_63_shifts :
    (powIter 63 ⟨2, 0x8000000000000000, 3⟩).exponent = 1#64 := by
  rw [exponent_projection]
  decide

theorem high_bit_after_64_shifts :
    (powIter 64 ⟨2, 0x8000000000000000, 3⟩).exponent = 0#64 :=
  exponent_terminal _

theorem all_ones_after_63_shifts :
    (powIter 63 ⟨2, 0xffffffffffffffff, 3⟩).exponent = 1#64 := by
  rw [exponent_projection]
  decide

theorem all_ones_after_64_shifts :
    (powIter 64 ⟨2, 0xffffffffffffffff, 3⟩).exponent = 0#64 :=
  exponent_terminal _

theorem zero_exponent_preserves_accumulator (n : Nat) (x z : BitVec 64) :
    (powIter n ⟨x, 0, z⟩).accumulator = z := powIter_zero_exponent n x z

set_option maxRecDepth 10000 in
theorem nonzero_initial_accumulator : (powIter 64 ⟨2, 1, 3⟩).accumulator = 6#64 := by
  apply toK_injective
  rw [powIter_accumulator]
  change toK (3#64) * (toK (2#64)) ^ 1 = toK (6#64)
  rw [pow_one, ← toK_mulRef]
  rfl

theorem actual_zero : Leanisa.Functions.gpow (0#64) = 1#64 := sail_gpow_zero

theorem actual_one : Leanisa.Functions.gpow (1#64) = 2#64 := gAddress_one

theorem actual_high_bit :
    Leanisa.Functions.gpow (0x8000000000000000#64) = 0xffffffff0000000a#64 :=
  Leanisa.Proofs.PowerLoopChecks.top_exponent_bit_is_processed

theorem actual_high_bit_image :
    toK (Leanisa.Functions.gpow (0x8000000000000000#64)) =
      (AdjoinRoot.root modulus) ^ (9223372036854775808 : Nat) := by
  rw [toK_gpow]
  rfl

theorem actual_all_ones : Leanisa.Functions.gpow (0xffffffffffffffff#64) = 1#64 :=
  sail_gpow_all_ones

theorem actual_all_ones_image : toK (Leanisa.Functions.gpow (0xffffffffffffffff#64)) = 1 := by
  rw [actual_all_ones, toK_one]

theorem largest_encoded_index :
    (BitVec.ofNat 64 (2^64 - 1)).toNat = 2^64 - 1 := encoded_index _ (by decide)

theorem first_wrapped_index : (BitVec.ofNat 64 (2^64)).toNat = 0 := by decide

theorem address_wrap : gAddress (2^64) = 1#64 := by
  exact sail_gpow_zero

theorem address_last : gAddress (2^64 - 1) = 1#64 := sail_gpow_all_ones

theorem recurrence_wrap_counterexample :
    gAddress ((2^64 - 1) + 1) ≠ Leanisa.Functions.advance (gAddress (2^64 - 1)) := by
  rw [show (2^64 - 1) + 1 = (2^64 : Nat) by decide, address_wrap, address_last]
  decide

theorem addition_wrap_counterexample :
    Leanisa.Functions.kmul (gAddress (2^64 - 1)) (gAddress 1) ≠
      gAddress ((2^64 - 1) + 1) := by
  rw [show (2^64 - 1) + 1 = (2^64 : Nat) by decide,
    address_last, gAddress_one, address_wrap, kmul_one_left]
  decide

theorem no_unbounded_recurrence :
    ¬ (∀ i : Nat, gAddress (i + 1) = Leanisa.Functions.advance (gAddress i)) := by
  intro h
  exact recurrence_wrap_counterexample (h (2^64 - 1))

theorem no_unbounded_addition :
    ¬ (∀ i j : Nat, Leanisa.Functions.kmul (gAddress i) (gAddress j) = gAddress (i + j)) := by
  intro h
  exact addition_wrap_counterexample (h (2^64 - 1) 1)

end Leanisa.Proofs.PolynomialExponentiationChecks
