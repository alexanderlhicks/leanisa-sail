import F1e5b

/-! Source-shaped extension inverse over actual extracted Sail arithmetic. -/

open Leanisa.Proofs.Quotient
open Leanisa.Proofs.Extension
open Leanisa.Proofs.Extension.F1e5b
open Leanisa.Proofs.BaseItoh
namespace Leanisa.Proofs.Extension.F1e5c

/-- The three base-field products performed by Rust's `mul_base` path. -/
def scaleWord (a : BitVec 192) (k : BitVec 64) : BitVec 192 :=
  pack
    (Leanisa.Functions.kmul (limb0 a) k)
    (Leanisa.Functions.kmul (limb1 a) k)
    (Leanisa.Functions.kmul (limb2 a) k)

/-- Scaling the packed limbs agrees with actual Sail extension multiplication. -/
theorem scaleWord_eq_emul_embed (a : BitVec 192) (k : BitVec 64) :
    scaleWord a k = Leanisa.Functions.emul a (Leanisa.Functions.embed_k k) := by
  apply toE_injective
  rw [scaleWord, toE_pack, toE_emul, toE_embed, toE_expansion]
  simp only [base_kmul]
  ring

/-- The two conjugates of zero multiply to zero. -/
theorem mWord_zero : mWord (0#192) = 0#192 := by
  apply toE_injective
  simp only [mWord, toE_emul, toE_frobWord, toE_zero]
  rw [zero_pow (by decide), zero_pow (by decide), mul_zero]

/-- Exact Lean model of Rust's norm, low-limb Itoh inverse, and three-limb scale. -/
def rustInvWord (a : BitVec 192) : BitVec 192 :=
  scaleWord (mWord a) (baseItohWord (limb0 (normWord a)))

theorem rustInvWord_zero : rustInvWord (0#192) = 0#192 := by
  rw [rustInvWord, mWord_zero, scaleWord_eq_emul_embed, emul_zero_left]

/-- Every nonzero word has the model as a right inverse for actual Sail `emul`. -/
theorem emul_rustInvWord (a : BitVec 192) (nonzero : a ≠ 0#192) :
    Leanisa.Functions.emul a (rustInvWord a) = 1#192 := by
  let k := limb0 (normWord a)
  calc
    Leanisa.Functions.emul a (rustInvWord a) =
        Leanisa.Functions.emul a
          (Leanisa.Functions.emul (mWord a) (Leanisa.Functions.embed_k (baseItohWord k))) := by
      rw [rustInvWord, scaleWord_eq_emul_embed]
    _ = Leanisa.Functions.emul (normWord a)
          (Leanisa.Functions.embed_k (baseItohWord k)) := by
      rw [normWord, emul_assoc]
    _ = Leanisa.Functions.embed_k (Leanisa.Functions.kmul k (baseItohWord k)) := by
      rw [normWord_eq_embed, emul_embed]
    _ = 1#192 := by
      rw [kmul_baseItohWord k (normWord_low_nonzero a nonzero)]
      rfl

/-- The source-shaped model equals the accepted binary-power reference, including zero. -/
theorem rustInvWord_eq_inverseRef (a : BitVec 192) :
    rustInvWord a = inverseRef a := by
  letI : Field ERing := extension_isField.toField
  by_cases h : a = 0#192
  · subst a
    rw [rustInvWord_zero, inverseRef_zero]
  · apply toE_injective
    have product := congrArg toE (emul_rustInvWord a h)
    rw [toE_emul, toE_one] at product
    rw [toE_inverseRef]
    exact eq_inv_of_mul_eq_one_right product

end Leanisa.Proofs.Extension.F1e5c
