/- Supported lower bound for the order of the fixed quotient root.
The proof transports accepted actual Sail certificates through the reviewed
ring-power map, then applies monoid-only order/divisibility facts. -/
import PolynomialExponentiation
import MonoidOrderBounds
import PowerCertificates

noncomputable section
namespace Leanisa.Proofs.Quotient
open Leanisa.Proofs.GeneratorOrder

/-- The accepted all-ones actual-output certificate supplies a positive period. -/
theorem root_period :
    (AdjoinRoot.root modulus) ^ (18446744073709551615 : Nat) = 1 := by
  have h := congrArg toK sail_gpow_all_ones
  rw [toK_gpow, encoded_index _ exponents_fit.1] at h
  change (AdjoinRoot.root modulus) ^ (18446744073709551615 : Nat) = toK (1#64) at h
  rw [toK_one] at h
  exact h

/-- First accepted actual-gpow inequality, with its exact natural exponent. -/
theorem root_pow_281470681808895_ne_one :
    (AdjoinRoot.root modulus) ^ (281470681808895 : Nat) ≠ 1 := by
  intro h
  apply sail_gpow_literal_281470681808895_ne_one
  apply toK_injective
  change toK (Leanisa.Functions.gpow (BitVec.ofNat 64 281470681808895)) = toK (1#64)
  rw [toK_gpow, encoded_index _ exponents_fit.2.1, toK_one]
  exact h

/-- Second accepted actual-gpow inequality, with its exact natural exponent. -/
theorem root_pow_2753074036095_ne_one :
    (AdjoinRoot.root modulus) ^ (2753074036095 : Nat) ≠ 1 := by
  intro h
  apply sail_gpow_literal_2753074036095_ne_one
  apply toK_injective
  change toK (Leanisa.Functions.gpow (BitVec.ofNat 64 2753074036095)) = toK (1#64)
  rw [toK_gpow, encoded_index _ exponents_fit.2.2, toK_one]
  exact h

theorem root_p_factor_power_ne_one :
    (AdjoinRoot.root modulus) ^ ((18446744073709551615 : Nat) / 65537) ≠ 1 := by
  simpa only [p_quotient] using root_pow_281470681808895_ne_one

theorem root_q_factor_power_ne_one :
    (AdjoinRoot.root modulus) ^ ((18446744073709551615 : Nat) / 6700417) ≠ 1 := by
  simpa only [q_quotient] using root_pow_2753074036095_ne_one

theorem root_order_dvd_period :
    orderOf (AdjoinRoot.root modulus) ∣ (18446744073709551615 : Nat) :=
  orderOf_dvd_of_pow_eq_one root_period

/-- A positive period rules out the zero order sentinel for infinite order. -/
theorem root_order_positive : 0 < orderOf (AdjoinRoot.root modulus) :=
  positive_order _ 18446744073709551615 period_positive root_period

theorem prime_p_dvd_root_order : (65537 : Nat) ∣ orderOf (AdjoinRoot.root modulus) :=
  prime_dvd_order _ 18446744073709551615 65537
    root_period p_prime p_dvd_period root_p_factor_power_ne_one

theorem prime_q_dvd_root_order : (6700417 : Nat) ∣ orderOf (AdjoinRoot.root modulus) :=
  prime_dvd_order _ 18446744073709551615 6700417
    root_period q_prime q_dvd_period root_q_factor_power_ne_one

theorem prime_product_dvd_root_order :
    (439125228929 : Nat) ∣ orderOf (AdjoinRoot.root modulus) := by
  rw [← pq_product]
  exact pq_coprime.mul_dvd_of_dvd_of_dvd prime_p_dvd_root_order prime_q_dvd_root_order

/-- Supported strict order bound for the fixed quotient root. No field,
cancellation, exact-full-order, or address-domain assertion is involved. -/
theorem root_order_gt_two_pow_32 : (2 : Nat)^32 < orderOf (AdjoinRoot.root modulus) := by
  exact bound_from_coprime_divisors _ 18446744073709551615 65537 6700417 (2^32)
    period_positive root_period pq_coprime prime_p_dvd_root_order prime_q_dvd_root_order
    bound_product

end Leanisa.Proofs.Quotient
