import PowerLoops

/-! Ordinary kernel-checked output of the extracted Sail exponentiator at
`(2^64 - 1) / 257`. -/
namespace Leanisa.Proofs
open Leanisa.Functions

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
private theorem quotient_257_reference :
    powRef (BitVec.ofNat 64 71777214294589695) = 0x56dfcf872019d0c1 := by
  decide

theorem sail_gpow_quotient_257 :
    gpow (BitVec.ofNat 64 71777214294589695) = 0x56dfcf872019d0c1 := by
  rw [sail_gpow_eq_powRef]
  exact quotient_257_reference

theorem sail_gpow_quotient_257_ne_one :
    gpow (BitVec.ofNat 64 71777214294589695) ≠ 1 := by
  rw [sail_gpow_quotient_257]
  decide

end Leanisa.Proofs
