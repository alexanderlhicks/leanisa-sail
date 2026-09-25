/-
Arithmetic divisor tables for the fixed period candidates in the
generator-order proof. The finite checks are discharged by the Lean kernel.
-/
import Mathlib.GroupTheory.OrderOfElement

namespace Leanisa.Proofs.GeneratorOrder

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem p_divisor_table :
    ∀ i : Fin 3, ∀ j : Fin 128,
      2 ≤ i.val * 128 + j.val → ¬ (i.val * 128 + j.val) ∣ 65537 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem q_divisor_table :
    ∀ i : Fin 21, ∀ j : Fin 128,
      2 ≤ i.val * 128 + j.val → ¬ (i.val * 128 + j.val) ∣ 6700417 := by decide

theorem p_prime : Nat.Prime 65537 := by
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨by decide, ?_⟩
  intro m lower upper
  have hs : Nat.sqrt 65537 < 257 := Nat.sqrt_lt.mpr (by decide)
  have heq : m / 128 * 128 + m % 128 = m := by omega
  have result := p_divisor_table ⟨m / 128, by omega⟩ ⟨m % 128, by omega⟩
  simpa only [heq] using result (by simpa only [heq] using lower)

theorem q_prime : Nat.Prime 6700417 := by
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨by decide, ?_⟩
  intro m lower upper
  have hs : Nat.sqrt 6700417 < 2589 := Nat.sqrt_lt.mpr (by decide)
  have heq : m / 128 * 128 + m % 128 = m := by omega
  have result := q_divisor_table ⟨m / 128, by omega⟩ ⟨m % 128, by omega⟩
  simpa only [heq] using result (by simpa only [heq] using lower)

theorem pq_coprime : Nat.Coprime 65537 6700417 := by decide
theorem pq_product : (65537 : Nat) * 6700417 = 439125228929 := by decide
theorem bound_product : (2 : Nat)^32 < 65537 * 6700417 := by decide
theorem p_dvd_period : (65537 : Nat) ∣ 18446744073709551615 := by decide
theorem q_dvd_period : (6700417 : Nat) ∣ 18446744073709551615 := by decide
theorem p_quotient : (18446744073709551615 : Nat) / 65537 = 281470681808895 := by decide
theorem q_quotient : (18446744073709551615 : Nat) / 6700417 = 2753074036095 := by decide
theorem period_positive : 0 < (18446744073709551615 : Nat) := by decide
theorem exponents_fit :
    (18446744073709551615 : Nat) < 2^64 ∧
    (281470681808895 : Nat) < 2^64 ∧
    (2753074036095 : Nat) < 2^64 := by decide

end Leanisa.Proofs.GeneratorOrder

