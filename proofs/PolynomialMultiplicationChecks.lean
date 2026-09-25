/- Directed kernel checks of exact update order, full-width termination,
and actual extracted multiplication. All bitvector computations use ordinary
kernel reduction; the native BitVec arithmetic instances are unchanged. -/
import PolynomialMultiplication

open Leanisa.Proofs.Quotient
namespace Leanisa.Proofs.PolynomialMultiplicationChecks

theorem zero_steps (s : MulState) : mulIter 0 s = s := rfl

theorem old_operands_low_bit : mulStep ⟨1, 1, 4⟩ = ⟨2, 0, 5⟩ := by decide

theorem old_operands_even_multiplier :
    mulStep ⟨0x8000000000000000, 2, 4⟩ = ⟨0x1b, 1, 4⟩ := by decide

theorem high_carry_nonzero_accumulator :
    mulStep ⟨0x8000000000000000, 1, 0x0123456789abcdef⟩ =
      ⟨0x1b, 0, 0x8123456789abcdef⟩ := by decide

theorem high_bit_after_63_shifts :
    (mulIter 63 ⟨1, 0x8000000000000000, 4⟩).multiplier = 1#64 := by
  rw [multiplier_projection]
  decide

theorem high_bit_after_64_shifts :
    (mulIter 64 ⟨1, 0x8000000000000000, 4⟩).multiplier = 0#64 := by
  exact multiplier_terminal _

theorem all_ones_after_63_shifts :
    (mulIter 63 ⟨1, 0xffffffffffffffff, 4⟩).multiplier = 1#64 := by
  rw [multiplier_projection]
  decide

theorem all_ones_after_64_shifts :
    (mulIter 64 ⟨1, 0xffffffffffffffff, 4⟩).multiplier = 0#64 := by
  exact multiplier_terminal _

/- As in accepted FieldLoopChecks, the bound accommodates ordinary reduction
of the complete, fixed 64-iteration computation. -/
set_option maxRecDepth 10000 in
theorem top_bit_pending_at_63 :
    (mulIter 63 ⟨1, 0x8000000000000000, 4⟩).accumulator = 4#64 := by decide

set_option maxRecDepth 10000 in
theorem top_bit_processed_at_64 :
    (mulIter 64 ⟨1, 0x8000000000000000, 4⟩).accumulator = 0x8000000000000004#64 := by
  decide

theorem arbitrary_accumulator_endpoint (x y z : BitVec 64) :
    (mulIter 64 ⟨x, y, z⟩).accumulator = z ^^^ Leanisa.Functions.kmul x y :=
  mulIter_accumulator_eq _

set_option maxRecDepth 10000 in
theorem actual_high_carry_low_multiplier :
    Leanisa.Functions.kmul (0x8000000000000000#64) (3#64) = 0x800000000000001b#64 := by
  rw [sail_kmul_eq_mulRef]
  decide

set_option maxRecDepth 10000 in
theorem actual_high_multiplier :
    Leanisa.Functions.kmul (3#64) (0x8000000000000000#64) = 0x800000000000001b#64 := by
  rw [sail_kmul_eq_mulRef]
  decide

set_option maxRecDepth 10000 in
theorem actual_all_ones_squared :
    Leanisa.Functions.kmul (0xffffffffffffffff#64) (0xffffffffffffffff#64) =
      0x5555555555555513#64 := by
  rw [sail_kmul_eq_mulRef]
  decide

set_option maxRecDepth 10000 in
theorem actual_all_ones_even_multiplier :
    Leanisa.Functions.kmul (0xffffffffffffffff#64) (2#64) = 0xffffffffffffffe5#64 := by
  rw [sail_kmul_eq_mulRef]
  decide

set_option maxRecDepth 10000 in
theorem actual_all_ones_multiplier :
    Leanisa.Functions.kmul (2#64) (0xffffffffffffffff#64) = 0xffffffffffffffe5#64 := by
  rw [sail_kmul_eq_mulRef]
  decide

theorem actual_zero_cases (a : BitVec 64) :
    Leanisa.Functions.kmul a (0#64) = 0#64 ∧ Leanisa.Functions.kmul (0#64) a = 0#64 :=
  ⟨kmul_zero_right a, kmul_zero_left a⟩

theorem actual_one_cases (a : BitVec 64) :
    Leanisa.Functions.kmul a (1#64) = a ∧ Leanisa.Functions.kmul (1#64) a = a :=
  ⟨kmul_one_right a, kmul_one_left a⟩

end Leanisa.Proofs.PolynomialMultiplicationChecks
