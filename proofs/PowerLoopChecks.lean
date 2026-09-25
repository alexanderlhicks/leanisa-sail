import PowerLoops

/-! Reference-state boundaries and a separate actual-result check. The source
tail checks concern the auxiliary copied loop, not hidden extracted registers. -/
namespace Leanisa.Proofs.PowerLoopChecks
open Leanisa.Functions

theorem empty_tail_preserves_all_registers (state : PowState) :
    sourcePowTail 64 state = state := by
  rw [source_pow_tail_eq 64 (by decide)]
  rfl

theorem last_iteration_uses_old_base (x z : KBits) :
    sourcePowTail 63 ⟨x, 1, z⟩ = ⟨mulRef x x, 0, mulRef z x⟩ := by
  rw [source_pow_tail_eq 63 (by decide)]
  simp [powIter, powStep]

theorem even_exponent_preserves_accumulator (x z : KBits) :
    sourcePowTail 63 ⟨x, 2, z⟩ = ⟨mulRef x x, 1, z⟩ := by
  rw [source_pow_tail_eq 63 (by decide)]
  simp [powIter, powStep]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
theorem two_iteration_nonzero_accumulator :
    sourcePowTail 62 ⟨0x8000000000000000, 3, 0x0123456789abcdef⟩ =
      ⟨0x7000000000001105, 0, 0xa40765c0640765eb⟩ := by
  rw [source_pow_tail_eq 62 (by decide)]
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
theorem top_exponent_bit_is_processed :
    gpow (BitVec.ofNat 64 9223372036854775808) = 0xffffffff0000000a := by
  rw [sail_gpow_eq_powRef]
  decide

end Leanisa.Proofs.PowerLoopChecks

#print axioms Leanisa.Proofs.PowerLoopChecks.empty_tail_preserves_all_registers
#print axioms Leanisa.Proofs.PowerLoopChecks.last_iteration_uses_old_base
#print axioms Leanisa.Proofs.PowerLoopChecks.even_exponent_preserves_accumulator
#print axioms Leanisa.Proofs.PowerLoopChecks.two_iteration_nonzero_accumulator
#print axioms Leanisa.Proofs.PowerLoopChecks.top_exponent_bit_is_processed
