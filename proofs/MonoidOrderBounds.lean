/-
Monoid order and divisibility bounds used to establish the exact order of
the fixed quotient root. The statements require only a monoid structure.
-/
import GeneratorOrderArithmetic

namespace Leanisa.Proofs.GeneratorOrder

theorem prime_dvd_order {M : Type*} [Monoid M] (r : M) (N p : Nat)
    (period : r^N = 1) (prime : Nat.Prime p) (divides : p ∣ N)
    (not_shorter : r^(N/p) ≠ 1) : p ∣ orderOf r := by
  by_contra hnot
  have coprime : Nat.Coprime p (orderOf r) := prime.coprime_iff_not_dvd.mpr hnot
  have order_divides : orderOf r ∣ N := orderOf_dvd_of_pow_eq_one period
  have product_divides : p * orderOf r ∣ N :=
    coprime.mul_dvd_of_dvd_of_dvd divides order_divides
  have shorter_divides : orderOf r ∣ N/p := Nat.dvd_div_of_mul_dvd product_divides
  exact not_shorter (orderOf_dvd_iff_pow_eq_one.mp shorter_divides)

theorem positive_order {M : Type*} [Monoid M] (r : M) (N : Nat)
    (positive : 0 < N) (period : r^N = 1) : 0 < orderOf r := by
  exact Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one period) positive

theorem bound_from_coprime_divisors {M : Type*} [Monoid M]
    (r : M) (N p q bound : Nat) (positive : 0 < N) (period : r^N = 1)
    (coprime : Nat.Coprime p q) (pd : p ∣ orderOf r) (qd : q ∣ orderOf r)
    (lower : bound < p*q) : bound < orderOf r := by
  have product_divides := coprime.mul_dvd_of_dvd_of_dvd pd qd
  exact Nat.lt_of_lt_of_le lower (Nat.le_of_dvd (positive_order r N positive period) product_divides)

/-- Still generic in an arbitrary monoid and supplied element; no Sail claim. -/
theorem specific_period_bound {M : Type*} [Monoid M] (r : M)
    (period : r^18446744073709551615 = 1)
    (not_p : r^281470681808895 ≠ 1)
    (not_q : r^2753074036095 ≠ 1) : 2^32 < orderOf r := by
  have pd := prime_dvd_order r 18446744073709551615 65537
    period p_prime p_dvd_period (by simpa only [p_quotient] using not_p)
  have qd := prime_dvd_order r 18446744073709551615 6700417
    period q_prime q_dvd_period (by simpa only [q_quotient] using not_q)
  exact bound_from_coprime_divisors r 18446744073709551615 65537 6700417 (2^32)
    period_positive period pq_coprime pd qd bound_product

end Leanisa.Proofs.GeneratorOrder

