import ExtensionField
import Mathlib.Data.Fintype.Units

/-! A binary-power inverse reference over the actual Sail extension multiplication. -/

section
open Polynomial Leanisa.Proofs.Quotient
namespace Leanisa.Proofs.Extension

noncomputable def coeffEquiv : ERing ≃ (Fin 3 → KRing) := by
  simpa only [cubic_natDegree] using
    (AdjoinRoot.powerBasisAux' cubic_monic).equivFun.toEquiv

noncomputable instance eFinite : Finite ERing :=
  Finite.of_injective coeffEquiv coeffEquiv.injective

theorem extension_card : Nat.card ERing = 2^192 := by
  rw [Nat.card_congr coeffEquiv, Nat.card_fun]
  simp only [F1eResearch.quotient_card, Nat.card_fin]
  norm_num

def wordEquiv : BitVec 192 ≃ Fin (2^192) where
  toFun a := a.toFin
  invFun a := ⟨a⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem word_card : Nat.card (BitVec 192) = 2^192 := by
  rw [Nat.card_congr wordEquiv]
  simp

theorem toE_surjective : Function.Surjective toE := by
  exact ((Nat.bijective_iff_injective_and_card toE).mpr
    ⟨toE_injective, word_card.trans extension_card.symm⟩).2

/-- A separate carrier prevents any changes to the native BitVec multiplication. -/
structure EWord where
  bits : BitVec 192

instance : One EWord := ⟨⟨1#192⟩⟩
instance : Mul EWord := ⟨fun a b => ⟨Leanisa.Functions.emul a.bits b.bits⟩⟩
instance : Semigroup EWord where
  mul_assoc a b c := by
    cases a with
    | mk a =>
      cases b with
      | mk b =>
        cases c with
        | mk c =>
          exact congrArg EWord.mk (emul_assoc a b c)

/-- Executable exponentiation by binary squaring, using Sail's actual `emul`. -/
def wordPow (a : BitVec 192) (n : Nat) : BitVec 192 :=
  (npowBinRec n (EWord.mk a)).bits

theorem wordPow_zero (a : BitVec 192) : wordPow a 0 = 1#192 := by
  rfl

theorem wordPow_succ (a : BitVec 192) (n : Nat) :
    wordPow a (n + 1) = Leanisa.Functions.emul (wordPow a n) a := by
  exact congrArg EWord.bits (npowBinRec_succ n (EWord.mk a))

theorem toE_wordPow (a : BitVec 192) (n : Nat) :
    toE (wordPow a n) = toE a ^ n := by
  induction n with
  | zero => simp only [wordPow_zero, toE_one, pow_zero]
  | succ n ih => rw [wordPow_succ, toE_emul, ih, pow_succ]

/-- A fixed exponent candidate; zero maps to zero. -/
def inverseRef (a : BitVec 192) : BitVec 192 := wordPow a (2^192 - 2)

theorem inverseRef_zero : inverseRef (0#192) = 0#192 := by
  apply toE_injective
  simp only [inverseRef, toE_wordPow, toE_zero]
  exact zero_pow (by decide)

private theorem finite_field_period {R : Type*} [Field R] [Finite R]
    (a : R) (nonzero : a ≠ 0) : a ^ (Nat.card R - 1) = 1 := by
  have h := pow_card_eq_one' (x := Units.mk0 a nonzero)
  have values := congrArg (fun u : Rˣ => u.val) h
  simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
    Nat.card_units] using values

/-- The executable word candidate is a right inverse for every nonzero word. -/
theorem emul_inverseRef (a : BitVec 192) (nonzero : a ≠ 0#192) :
    Leanisa.Functions.emul a (inverseRef a) = 1#192 := by
  letI : Field ERing := extension_isField.toField
  have nz : toE a ≠ 0 := by
    intro h
    exact nonzero (toE_injective (h.trans toE_zero.symm))
  apply toE_injective
  rw [toE_emul, toE_one, inverseRef, toE_wordPow]
  rw [← pow_succ']
  have hexp : 2^192 - 2 + 1 = Nat.card ERing - 1 := by
    rw [extension_card]
    omega
  rw [hexp]
  exact finite_field_period _ nz

/-- The executable candidate agrees with inversion in the quotient field, including zero. -/
theorem toE_inverseRef (a : BitVec 192) :
    (letI : Field ERing := extension_isField.toField
     toE (inverseRef a) = (toE a)⁻¹) := by
  letI : Field ERing := extension_isField.toField
  by_cases h : a = 0#192
  · subst a
    rw [inverseRef_zero, toE_zero, inv_zero]
  · have product := congrArg toE (emul_inverseRef a h)
    rw [toE_emul, toE_one] at product
    exact eq_inv_of_mul_eq_one_right product

end Leanisa.Proofs.Extension
