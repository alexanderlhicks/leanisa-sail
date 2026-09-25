/-
Directed checks of the supported generator-order facts. These theorems
exercise exact divisor and order boundaries used by the quotient-root proof.
-/
import GeneratorOrder

namespace Leanisa.Proofs.GeneratorOrder

theorem changed_p_composite : ¬Nat.Prime 65535 := by
  intro hp
  have h := hp.eq_one_or_self_of_dvd 3 (by decide)
  rcases h with h | h <;> omega

theorem zero_order_divisors :
    65537 ∣ orderOf (0 : Nat) ∧ 6700417 ∣ orderOf (0 : Nat) := by
  rw [orderOf_zero]
  exact ⟨Nat.dvd_zero _, Nat.dvd_zero _⟩

theorem zero_period : (0 : Nat)^0 = 1 := by rfl

theorem zero_order_not_large : ¬2^32 < orderOf (0 : Nat) := by
  rw [orderOf_zero]
  decide

theorem zero_no_positive_period : ∀ n : Nat, 0 < n → (0 : Nat)^n ≠ 1 := by
  intro n hn
  simp [Nat.ne_of_gt hn]

/-- The period contains p²; the prime-divisibility argument still applies. -/
theorem repeated_prime_factor {M : Type*} [Monoid M] (r : M)
    (period : r^4 = 1) (not_shorter : r^2 ≠ 1) : 2 ∣ orderOf r := by
  exact prime_dvd_order r 4 2 period (by decide) (by decide) not_shorter

theorem unit_positive_order : 0 < orderOf (1 : Nat) := by
  simp

theorem actual_root_order_not_zero : orderOf (AdjoinRoot.root Quotient.modulus) ≠ 0 :=
  Nat.ne_of_gt Quotient.root_order_positive

theorem actual_root_supported_boundary :
    (4294967296 : Nat) < orderOf (AdjoinRoot.root Quotient.modulus) :=
  Quotient.root_order_gt_two_pow_32

theorem p_quotient_encoding_bound :
    (18446744073709551615 : Nat) / 65537 < 2^64 := by
  rw [p_quotient]
  exact exponents_fit.2.1

theorem q_quotient_encoding_bound :
    (18446744073709551615 : Nat) / 6700417 < 2^64 := by
  rw [q_quotient]
  exact exponents_fit.2.2

end Leanisa.Proofs.GeneratorOrder
