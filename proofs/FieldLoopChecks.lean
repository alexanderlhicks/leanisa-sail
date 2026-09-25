import FieldLoops

/-! Kernel-checked interface boundaries. Closed checks use ordinary reduction,
with auxiliary source-state boundaries distinguished from the actual Sail
multiplication-result check. -/
namespace Leanisa.Proofs.FieldLoopChecks
open Leanisa.Functions

theorem empty_tail_preserves_all_registers (state : MulState) :
    sourceMulTail 64 state = state := by
  rw [source_mul_tail_eq 64 (by decide)]
  rfl

theorem last_iteration_preserves_old_operands (x z : KBits) :
    sourceMulTail 63 ⟨x, 1, z⟩ = ⟨xtime x, 0, z ^^^ x⟩ := by
  rw [source_mul_tail_eq 63 (by decide)]
  simp [mulIter, mulStep]

theorem high_carry_with_accumulator :
    sourceMulTail 63 ⟨0x8000000000000000, 1, 0x0123456789abcdef⟩ =
      ⟨0x1b, 0, 0x8123456789abcdef⟩ := by
  rw [source_mul_tail_eq 63 (by decide)]
  decide

theorem two_iteration_suffix :
    sourceMulTail 62 ⟨0x8000000000000000, 3, 0x0123456789abcdef⟩ =
      ⟨0x36, 0, 0x8123456789abcdf4⟩ := by
  rw [source_mul_tail_eq 62 (by decide)]
  decide

set_option maxRecDepth 10000 in
theorem top_multiplier_bit_is_processed :
    kmul 1 0x8000000000000000 = 0x8000000000000000 := by
  rw [sail_kmul_eq_mulRef]
  decide

end Leanisa.Proofs.FieldLoopChecks

#print axioms Leanisa.Proofs.FieldLoopChecks.empty_tail_preserves_all_registers
#print axioms Leanisa.Proofs.FieldLoopChecks.last_iteration_preserves_old_operands
#print axioms Leanisa.Proofs.FieldLoopChecks.high_carry_with_accumulator
#print axioms Leanisa.Proofs.FieldLoopChecks.two_iteration_suffix
#print axioms Leanisa.Proofs.FieldLoopChecks.top_multiplier_bit_is_processed
