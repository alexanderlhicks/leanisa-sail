import F1eCardinality
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Field.IsField

noncomputable section
namespace F1eResearch

theorem power_inverse {R : Type*} [CommRing R] (r : R) (N : Nat)
    (period : r^N = 1) (i : Fin N) : r ^ i.val * r ^ (N - i.val) = 1 := by
  rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt i.isLt), period]

theorem power_nonzero {R : Type*} [CommRing R] [Nontrivial R]
    (r : R) (N : Nat) (period : r^N = 1) (i : Fin N) : r ^ i.val ≠ 0 := by
  intro zero
  have inverse := power_inverse r N period i
  rw [zero, zero_mul] at inverse
  exact zero_ne_one inverse

theorem field_of_order_card {R : Type*} [CommRing R] [Nontrivial R]
    (r : R) (N : Nat) (exactOrder : orderOf r = N) (card : Nat.card R = N+1) : IsField R := by
  letI : Finite R := Nat.finite_of_card_ne_zero (by omega)
  have period : r^N = 1 := by rw [← exactOrder]; exact pow_orderOf_eq_one r
  let entry : Option (Fin N) → R := fun i => match i with | none => 0 | some i => r ^ i.val
  have injective : Function.Injective entry := by
    intro a b equal
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j => exact False.elim (power_nonzero r N period j equal.symm)
    | some i =>
      cases b with
      | none => exact False.elim (power_nonzero r N period i equal)
      | some j =>
        have exponents : i.val = j.val :=
          pow_injOn_Iio_orderOf (x := r) (by simpa only [Set.mem_Iio, exactOrder] using i.isLt)
            (by simpa only [Set.mem_Iio, exactOrder] using j.isLt) equal
        exact congrArg some (Fin.ext exponents)
  have sameCard : Nat.card (Option (Fin N)) = Nat.card R := by
    rw [card]
    simp [Nat.card_eq_fintype_card]
  have cover : Function.Surjective entry :=
    ((Nat.bijective_iff_injective_and_card entry).mpr ⟨injective, sameCard⟩).2
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a nonzero
  obtain ⟨i, maps⟩ := cover a
  cases i with
  | none => exact False.elim (nonzero maps.symm)
  | some i =>
    refine ⟨r ^ (N - i.val), ?_⟩
    rw [← maps]
    exact power_inverse r N period i

/-- The missing premise is exact order, not the accepted supported lower bound. -/
theorem base_field_if_exact_order
    (exactOrder : orderOf (AdjoinRoot.root Leanisa.Proofs.Quotient.modulus) = 18446744073709551615) :
    IsField Leanisa.Proofs.Quotient.KRing := by
  apply field_of_order_card (AdjoinRoot.root Leanisa.Proofs.Quotient.modulus)
    18446744073709551615 exactOrder
  rw [quotient_card]
  decide

end F1eResearch
