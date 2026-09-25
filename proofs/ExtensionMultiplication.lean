import ExtensionRepresentation
import PolynomialMultiplication
import Mathlib.Tactic.Ring

/-
Actual extracted extension multiplication in the cubic quotient. The
nine-product packing theorem unfolds the Sail model, and base products use
the multiplication refinement proved in PolynomialMultiplication.
-/

noncomputable section
open Leanisa.Proofs.Quotient
namespace Leanisa.Proofs.Extension

theorem base_kmul (a b : BitVec 64) :
    base (Leanisa.Functions.kmul a b) = base a * base b := by
  simp only [base, toK_kmul, map_mul]

theorem cubic_product (a0 a1 a2 b0 b1 b2 : ERing) :
    (a0 + a1*y + a2*y^2) * (b0 + b1*y + b2*y^2) =
    (a0*b0 + (a1*b2 + a2*b1)) +
    ((a0*b1 + a1*b0) + (a1*b2 + a2*b1) + a2*b2)*y +
    ((a0*b2 + a1*b1 + a2*b0) + a2*b2)*y^2 := by
  calc
    _ = a0*b0 + (a0*b1+a1*b0)*y + (a0*b2+a1*b1+a2*b0)*y^2 +
        (a1*b2+a2*b1)*y^3 + (a2*b2)*y^4 := by ring
    _ = _ := by rw [y_cubic, y_fourth]; ring

theorem actual_emul_packing (a b : BitVec 192) :
    Leanisa.Functions.emul a b =
      pack
        (Leanisa.Functions.kmul (limb0 a) (limb0 b) ^^^
          (Leanisa.Functions.kmul (limb1 a) (limb2 b) ^^^ Leanisa.Functions.kmul (limb2 a) (limb1 b)))
        ((Leanisa.Functions.kmul (limb0 a) (limb1 b) ^^^ Leanisa.Functions.kmul (limb1 a) (limb0 b)) ^^^
          (Leanisa.Functions.kmul (limb1 a) (limb2 b) ^^^ Leanisa.Functions.kmul (limb2 a) (limb1 b)) ^^^
          Leanisa.Functions.kmul (limb2 a) (limb2 b))
        ((Leanisa.Functions.kmul (limb0 a) (limb2 b) ^^^ Leanisa.Functions.kmul (limb1 a) (limb1 b) ^^^
          Leanisa.Functions.kmul (limb2 a) (limb0 b)) ^^^ Leanisa.Functions.kmul (limb2 a) (limb2 b)) := by rfl

/-- This bridge is about the actual extracted function, not an assumed word algorithm. -/
theorem toE_emul (a b : BitVec 192) : toE (Leanisa.Functions.emul a b) = toE a * toE b := by
  rw [actual_emul_packing, toE_pack]
  simp only [base_xor, base_kmul]
  rw [toE_expansion a, toE_expansion b]
  exact (cubic_product _ _ _ _ _ _).symm

theorem emul_zero_right (a : BitVec 192) : Leanisa.Functions.emul a (0#192) = 0#192 := by
  apply toE_injective
  simp only [toE_emul, toE_zero, mul_zero]

theorem emul_zero_left (a : BitVec 192) : Leanisa.Functions.emul (0#192) a = 0#192 := by
  apply toE_injective
  simp only [toE_emul, toE_zero, zero_mul]

theorem emul_one_right (a : BitVec 192) : Leanisa.Functions.emul a (1#192) = a := by
  apply toE_injective
  simp only [toE_emul, toE_one, mul_one]

theorem emul_one_left (a : BitVec 192) : Leanisa.Functions.emul (1#192) a = a := by
  apply toE_injective
  simp only [toE_emul, toE_one, one_mul]

theorem emul_comm (a b : BitVec 192) :
    Leanisa.Functions.emul a b = Leanisa.Functions.emul b a := by
  apply toE_injective
  simp only [toE_emul, mul_comm]

theorem emul_assoc (a b c : BitVec 192) :
    Leanisa.Functions.emul (Leanisa.Functions.emul a b) c =
      Leanisa.Functions.emul a (Leanisa.Functions.emul b c) := by
  apply toE_injective
  simp only [toE_emul, mul_assoc]

theorem emul_xor_right (a b c : BitVec 192) :
    Leanisa.Functions.emul a (b ^^^ c) =
      Leanisa.Functions.emul a b ^^^ Leanisa.Functions.emul a c := by
  apply toE_injective
  simp only [toE_emul, toE_xor, mul_add]

theorem emul_xor_left (a b c : BitVec 192) :
    Leanisa.Functions.emul (a ^^^ b) c =
      Leanisa.Functions.emul a c ^^^ Leanisa.Functions.emul b c := by
  apply toE_injective
  simp only [toE_emul, toE_xor, add_mul]

/-- The actual low-limb embedding preserves actual base multiplication. -/
theorem emul_embed (a b : BitVec 64) :
    Leanisa.Functions.emul (Leanisa.Functions.embed_k a) (Leanisa.Functions.embed_k b) =
      Leanisa.Functions.embed_k (Leanisa.Functions.kmul a b) := by
  apply toE_injective
  simp only [toE_emul, toE_embed, base_kmul]

end Leanisa.Proofs.Extension
