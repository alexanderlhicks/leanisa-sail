import PowerLoops

/-! Closed outputs of the actual extracted exponentiator. These certificates
use its exact-order structural evaluator and ordinary kernel reduction. They
assert no ring-power interpretation, period, or generator order. All natural
inputs are explicitly truncated to 64 bits by `BitVec.ofNat`. -/
namespace Leanisa.Proofs
open Leanisa.Functions

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
private theorem all_ones_reference :
    powRef (BitVec.ofNat 64 18446744073709551615) = 1 := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
private theorem literal_281470681808895_reference :
    powRef (BitVec.ofNat 64 281470681808895) = 0x1c1e79669b95a7ce := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
private theorem literal_2753074036095_reference :
    powRef (BitVec.ofNat 64 2753074036095) = 0x00f542601703f991 := by
  decide

theorem sail_gpow_all_ones :
    gpow (BitVec.ofNat 64 18446744073709551615) = 1 := by
  rw [sail_gpow_eq_powRef]
  exact all_ones_reference

theorem sail_gpow_literal_281470681808895 :
    gpow (BitVec.ofNat 64 281470681808895) = 0x1c1e79669b95a7ce := by
  rw [sail_gpow_eq_powRef]
  exact literal_281470681808895_reference

theorem sail_gpow_literal_2753074036095 :
    gpow (BitVec.ofNat 64 2753074036095) = 0x00f542601703f991 := by
  rw [sail_gpow_eq_powRef]
  exact literal_2753074036095_reference

theorem sail_gpow_literal_281470681808895_ne_one :
    gpow (BitVec.ofNat 64 281470681808895) ≠ 1 := by
  rw [sail_gpow_literal_281470681808895]
  decide

theorem sail_gpow_literal_2753074036095_ne_one :
    gpow (BitVec.ofNat 64 2753074036095) ≠ 1 := by
  rw [sail_gpow_literal_2753074036095]
  decide

end Leanisa.Proofs

#print axioms Leanisa.Proofs.sail_gpow_all_ones
#print axioms Leanisa.Proofs.sail_gpow_literal_281470681808895
#print axioms Leanisa.Proofs.sail_gpow_literal_2753074036095
#print axioms Leanisa.Proofs.sail_gpow_literal_281470681808895_ne_one
#print axioms Leanisa.Proofs.sail_gpow_literal_2753074036095_ne_one
