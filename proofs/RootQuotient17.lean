import PowerLoops

/-! Ordinary kernel-checked output of the extracted Sail exponentiator at
`(2^64 - 1) / 17`. -/
namespace Leanisa.Proofs
open Leanisa.Functions

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
private theorem quotient_17_reference :
    powRef (BitVec.ofNat 64 1085102592571150095) = 0x0cf7b828f270c0db := by
  decide

theorem sail_gpow_quotient_17 :
    gpow (BitVec.ofNat 64 1085102592571150095) = 0x0cf7b828f270c0db := by
  rw [sail_gpow_eq_powRef]
  exact quotient_17_reference

theorem sail_gpow_quotient_17_ne_one :
    gpow (BitVec.ofNat 64 1085102592571150095) ≠ 1 := by
  rw [sail_gpow_quotient_17]
  decide

end Leanisa.Proofs
