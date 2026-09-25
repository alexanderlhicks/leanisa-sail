import ExtensionMultiplication
import BaseField
import F1eCardinality
import Mathlib.Data.Fintype.Units
import Mathlib.Tactic.Ring

/-
The accepted extension polynomial is X^3 + X + 1 over the accepted
64-bit base quotient. All Field and irreducibility instances here are local.
-/

noncomputable section
open Polynomial Leanisa.Proofs.Quotient
namespace Leanisa.Proofs.Extension

private theorem add_self_zero (a : KRing) : a + a = 0 := by
  have h : -a = a := ZModModule.neg_eq_self _
  calc
    a + a = -a + a := congrArg (fun x => x + a) h.symm
    _ = 0 := neg_add_cancel a

private theorem cubic_root_period (r : KRing) (root : r^3 = r + 1) : r^7 = 1 := by
  have fourth : r^4 = r^2 + r := by
    rw [show 4 = 3 + 1 by decide, pow_succ, root, add_mul, one_mul, ← pow_two]
  calc
    r^7 = r^3 * r^4 := by rw [← pow_add]
    _ = (r + 1) * (r^2 + r) := by rw [root, fourth]
    _ = r^3 + (r^2 + r^2) + r := by ring
    _ = (r + r) + 1 := by rw [root, add_self_zero, add_zero]; ac_rfl
    _ = 1 := by rw [add_self_zero, zero_add]

private theorem finite_field_period {R : Type*} [Field R] (a : R) (nonzero : a ≠ 0) :
    a ^ (Nat.card R - 1) = 1 := by
  have h := pow_card_eq_one' (x := Units.mk0 a nonzero)
  have values := congrArg (fun u : Rˣ => u.val) h
  simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
    Nat.card_units] using values

private theorem cubic_rootless (r : KRing) : r^3 ≠ r + 1 := by
  letI : Field KRing := base_isField.toField
  intro root
  have nonzero : r ≠ 0 := by
    intro zero
    rw [zero, zero_pow (by decide), zero_add] at root
    exact zero_ne_one root
  have period : r ^ 18446744073709551615 = 1 := by
    simpa only [F1eResearch.quotient_card] using finite_field_period r nonzero
  have divides7 := orderOf_dvd_of_pow_eq_one (cubic_root_period r root)
  have dividesN := orderOf_dvd_of_pow_eq_one period
  have coprime : Nat.Coprime 7 18446744073709551615 := by decide
  have dividesOne : orderOf r ∣ 1 := by
    simpa only [coprime.gcd_eq_one] using Nat.dvd_gcd divides7 dividesN
  have isOne : r = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp dividesOne)
  rw [isOne, one_pow, add_self_zero] at root
  exact one_ne_zero root

/-- The accepted cubic `X^3 + X + 1` is irreducible over the concrete base field. -/
theorem cubic_irreducible : Irreducible cubic := by
  letI : Field KRing := base_isField.toField
  have notOne : cubic ≠ 1 := by
    intro eq
    have deg := cubic_natDegree
    rw [eq, natDegree_one] at deg
    contradiction
  rw [cubic_monic.irreducible_iff_lt_natDegree_lt notOne]
  intro q monic degree divides
  have linear : q.natDegree = 1 := by
    simp only [Finset.mem_Ioc, cubic_natDegree] at degree
    omega
  have zero : eval (-(q.coeff 0)) q = 0 := by
    rw [monic.eq_X_add_C linear]
    simp
  have root := eval_eq_zero_of_dvd_of_eval_eq_zero divides zero
  simp only [cubic, eval_add, eval_pow, eval_X, eval_one] at root
  have relation : (-(q.coeff 0))^3 = -(q.coeff 0) + 1 := by
    simpa only [ZModModule.neg_eq_self] using eq_neg_of_add_eq_zero_left root
  exact cubic_rootless _ relation

/-- The concrete cubic AdjoinRoot quotient is a field. -/
theorem extension_isField : IsField ERing := by
  letI : Field KRing := base_isField.toField
  letI : Fact (Irreducible cubic) := ⟨cubic_irreducible⟩
  exact Field.toIsField ERing

end Leanisa.Proofs.Extension
