import PowerLoops

/-! Ordinary kernel-checked output of the extracted Sail exponentiator at
`(2^64 - 1) / 641`. -/
namespace Leanisa.Proofs
open Leanisa.Functions

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
private theorem quotient_641_reference :
    powRef (BitVec.ofNat 64 28778071877862015) = 0x6bf808f7824282a2 := by
  decide

theorem sail_gpow_quotient_641 :
    gpow (BitVec.ofNat 64 28778071877862015) = 0x6bf808f7824282a2 := by
  rw [sail_gpow_eq_powRef]
  exact quotient_641_reference

theorem sail_gpow_quotient_641_ne_one :
    gpow (BitVec.ofNat 64 28778071877862015) ≠ 1 := by
  rw [sail_gpow_quotient_641]
  decide

end Leanisa.Proofs
