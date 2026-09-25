import PowerLoops

/-! Ordinary kernel-checked output of the extracted Sail exponentiator at
`(2^64 - 1) / 3`. -/
namespace Leanisa.Proofs
open Leanisa.Functions

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
private theorem quotient_3_reference :
    powRef (BitVec.ofNat 64 6148914691236517205) = 0x19c9369f278adc02 := by
  decide

theorem sail_gpow_quotient_3 :
    gpow (BitVec.ofNat 64 6148914691236517205) = 0x19c9369f278adc02 := by
  rw [sail_gpow_eq_powRef]
  exact quotient_3_reference

theorem sail_gpow_quotient_3_ne_one :
    gpow (BitVec.ofNat 64 6148914691236517205) ≠ 1 := by
  rw [sail_gpow_quotient_3]
  decide

end Leanisa.Proofs
