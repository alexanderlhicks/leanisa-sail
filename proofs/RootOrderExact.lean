import GeneratorOrder
import RootQuotient3
import RootQuotient5
import RootQuotient17
import RootQuotient257
import RootQuotient641

/-! Exact multiplicative order of the distinguished base quotient root. The
five new actual Sail outputs are proved in separate ordinary-kernel modules. -/
noncomputable section
namespace Leanisa.Proofs.Quotient
open Leanisa.Proofs.GeneratorOrder

/-- The actual extracted gpow output excludes the shorter root power for 3. -/
theorem root_pow_quotient_3_ne_one :
    (AdjoinRoot.root modulus) ^ (6148914691236517205 : Nat) ≠ 1 := by
  intro h
  apply sail_gpow_quotient_3_ne_one
  apply toK_injective
  change toK (Leanisa.Functions.gpow (BitVec.ofNat 64 6148914691236517205)) = toK (1#64)
  rw [toK_gpow, encoded_index _ (by decide : 6148914691236517205 < 2^64), toK_one]
  exact h

theorem prime_3_dvd_root_order :
    (3 : Nat) ∣ orderOf (AdjoinRoot.root modulus) := by
  exact prime_dvd_order _ 18446744073709551615 3
    root_period (by decide : Nat.Prime 3)
    (by decide : (3 : Nat) ∣ 18446744073709551615)
    (by simpa only [show (18446744073709551615 : Nat) / 3 = 6148914691236517205 by decide]
      using root_pow_quotient_3_ne_one)

/-- The actual extracted gpow output excludes the shorter root power for 5. -/
theorem root_pow_quotient_5_ne_one :
    (AdjoinRoot.root modulus) ^ (3689348814741910323 : Nat) ≠ 1 := by
  intro h
  apply sail_gpow_quotient_5_ne_one
  apply toK_injective
  change toK (Leanisa.Functions.gpow (BitVec.ofNat 64 3689348814741910323)) = toK (1#64)
  rw [toK_gpow, encoded_index _ (by decide : 3689348814741910323 < 2^64), toK_one]
  exact h

theorem prime_5_dvd_root_order :
    (5 : Nat) ∣ orderOf (AdjoinRoot.root modulus) := by
  exact prime_dvd_order _ 18446744073709551615 5
    root_period (by decide : Nat.Prime 5)
    (by decide : (5 : Nat) ∣ 18446744073709551615)
    (by simpa only [show (18446744073709551615 : Nat) / 5 = 3689348814741910323 by decide]
      using root_pow_quotient_5_ne_one)

/-- The actual extracted gpow output excludes the shorter root power for 17. -/
theorem root_pow_quotient_17_ne_one :
    (AdjoinRoot.root modulus) ^ (1085102592571150095 : Nat) ≠ 1 := by
  intro h
  apply sail_gpow_quotient_17_ne_one
  apply toK_injective
  change toK (Leanisa.Functions.gpow (BitVec.ofNat 64 1085102592571150095)) = toK (1#64)
  rw [toK_gpow, encoded_index _ (by decide : 1085102592571150095 < 2^64), toK_one]
  exact h

theorem prime_17_dvd_root_order :
    (17 : Nat) ∣ orderOf (AdjoinRoot.root modulus) := by
  exact prime_dvd_order _ 18446744073709551615 17
    root_period (by decide : Nat.Prime 17)
    (by decide : (17 : Nat) ∣ 18446744073709551615)
    (by simpa only [show (18446744073709551615 : Nat) / 17 = 1085102592571150095 by decide]
      using root_pow_quotient_17_ne_one)

/-- The actual extracted gpow output excludes the shorter root power for 257. -/
theorem root_pow_quotient_257_ne_one :
    (AdjoinRoot.root modulus) ^ (71777214294589695 : Nat) ≠ 1 := by
  intro h
  apply sail_gpow_quotient_257_ne_one
  apply toK_injective
  change toK (Leanisa.Functions.gpow (BitVec.ofNat 64 71777214294589695)) = toK (1#64)
  rw [toK_gpow, encoded_index _ (by decide : 71777214294589695 < 2^64), toK_one]
  exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem prime_257_dvd_root_order :
    (257 : Nat) ∣ orderOf (AdjoinRoot.root modulus) := by
  exact prime_dvd_order _ 18446744073709551615 257
    root_period (by decide : Nat.Prime 257)
    (by decide : (257 : Nat) ∣ 18446744073709551615)
    (by simpa only [show (18446744073709551615 : Nat) / 257 = 71777214294589695 by decide]
      using root_pow_quotient_257_ne_one)

/-- The actual extracted gpow output excludes the shorter root power for 641. -/
theorem root_pow_quotient_641_ne_one :
    (AdjoinRoot.root modulus) ^ (28778071877862015 : Nat) ≠ 1 := by
  intro h
  apply sail_gpow_quotient_641_ne_one
  apply toK_injective
  change toK (Leanisa.Functions.gpow (BitVec.ofNat 64 28778071877862015)) = toK (1#64)
  rw [toK_gpow, encoded_index _ (by decide : 28778071877862015 < 2^64), toK_one]
  exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem prime_641_dvd_root_order :
    (641 : Nat) ∣ orderOf (AdjoinRoot.root modulus) := by
  exact prime_dvd_order _ 18446744073709551615 641
    root_period (by decide : Nat.Prime 641)
    (by decide : (641 : Nat) ∣ 18446744073709551615)
    (by simpa only [show (18446744073709551615 : Nat) / 641 = 28778071877862015 by decide]
      using root_pow_quotient_641_ne_one)

private theorem first_through_3_dvd_root_order :
    (1317375686787 : Nat) ∣ orderOf (AdjoinRoot.root modulus) := by
  have hc : Nat.Coprime 439125228929 3 := by decide
  have hd := hc.mul_dvd_of_dvd_of_dvd prime_product_dvd_root_order prime_3_dvd_root_order
  simpa only [show (439125228929 : Nat) * 3 = 1317375686787 by decide] using hd

private theorem first_through_5_dvd_root_order :
    (6586878433935 : Nat) ∣ orderOf (AdjoinRoot.root modulus) := by
  have hc : Nat.Coprime 1317375686787 5 := by decide
  have hd := hc.mul_dvd_of_dvd_of_dvd first_through_3_dvd_root_order prime_5_dvd_root_order
  simpa only [show (1317375686787 : Nat) * 5 = 6586878433935 by decide] using hd

private theorem first_through_17_dvd_root_order :
    (111976933376895 : Nat) ∣ orderOf (AdjoinRoot.root modulus) := by
  have hc : Nat.Coprime 6586878433935 17 := by decide
  have hd := hc.mul_dvd_of_dvd_of_dvd first_through_5_dvd_root_order prime_17_dvd_root_order
  simpa only [show (6586878433935 : Nat) * 17 = 111976933376895 by decide] using hd

private theorem first_through_257_dvd_root_order :
    (28778071877862015 : Nat) ∣ orderOf (AdjoinRoot.root modulus) := by
  have hc : Nat.Coprime 111976933376895 257 := by decide
  have hd := hc.mul_dvd_of_dvd_of_dvd first_through_17_dvd_root_order prime_257_dvd_root_order
  simpa only [show (111976933376895 : Nat) * 257 = 28778071877862015 by decide] using hd

private theorem first_through_641_dvd_root_order :
    (18446744073709551615 : Nat) ∣ orderOf (AdjoinRoot.root modulus) := by
  have hc : Nat.Coprime 28778071877862015 641 := by decide
  have hd := hc.mul_dvd_of_dvd_of_dvd first_through_257_dvd_root_order prime_641_dvd_root_order
  simpa only [show (28778071877862015 : Nat) * 641 = 18446744073709551615 by decide] using hd

/-- Exact full nonzero order follows from the accepted period and all seven
prime divisors, each supported by an actual extracted gpow certificate. -/
theorem root_order_exact :
    orderOf (AdjoinRoot.root modulus) = (18446744073709551615 : Nat) := by
  exact Nat.dvd_antisymm root_order_dvd_period first_through_641_dvd_root_order

end Leanisa.Proofs.Quotient
