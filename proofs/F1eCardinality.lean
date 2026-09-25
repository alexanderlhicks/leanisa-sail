import ExtensionRepresentation

noncomputable section
open Polynomial Leanisa.Proofs.Quotient
namespace F1eResearch

def coeffEquiv : KRing ≃ (Fin 64 → ZMod 2) := by
  simpa only [modulus_natDegree] using
    (AdjoinRoot.powerBasisAux' modulus_monic).equivFun.toEquiv

instance kFinite : Finite KRing := Finite.of_injective coeffEquiv coeffEquiv.injective

theorem quotient_card : Nat.card KRing = 2^64 := by
  rw [Nat.card_congr coeffEquiv, Nat.card_fun]
  simp [Nat.card_eq_fintype_card]

def wordEquiv : BitVec 64 ≃ Fin (2^64) where
  toFun a := a.toFin
  invFun a := ⟨a⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem word_card : Nat.card (BitVec 64) = 2^64 := by
  rw [Nat.card_congr wordEquiv]
  simp

theorem toK_surjective : Function.Surjective toK := by
  exact ((Nat.bijective_iff_injective_and_card toK).mpr
    ⟨toK_injective, word_card.trans quotient_card.symm⟩).2

end F1eResearch
