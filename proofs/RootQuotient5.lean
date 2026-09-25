import PowerLoops

/-! Ordinary kernel-checked output of the extracted Sail exponentiator at
`(2^64 - 1) / 5`. -/
namespace Leanisa.Proofs
open Leanisa.Functions

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
private theorem quotient_5_reference :
    powRef (BitVec.ofNat 64 3689348814741910323) = 0x5db84357ce785d09 := by
  decide

theorem sail_gpow_quotient_5 :
    gpow (BitVec.ofNat 64 3689348814741910323) = 0x5db84357ce785d09 := by
  rw [sail_gpow_eq_powRef]
  exact quotient_5_reference

theorem sail_gpow_quotient_5_ne_one :
    gpow (BitVec.ofNat 64 3689348814741910323) ≠ 1 := by
  rw [sail_gpow_quotient_5]
  decide

end Leanisa.Proofs
