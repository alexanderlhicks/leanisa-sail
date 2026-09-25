import BaseItoh
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Fintype.Units

/-! Exact Frobenius shuffle and norm over Sail `emul`. -/

open Leanisa.Proofs.Quotient
namespace Leanisa.Proofs.Extension.F1e5b

/-- The Rust source's coefficient shuffle, implemented on Sail's three packed limbs. -/
def frobWord (a : BitVec 192) : BitVec 192 :=
  pack (limb0 a) (limb2 a) (limb1 a ^^^ limb2 a)

theorem frobWord_limbs (a : BitVec 192) :
    limb0 (frobWord a) = limb0 a ∧
    limb1 (frobWord a) = limb2 a ∧
    limb2 (frobWord a) = limb1 a ^^^ limb2 a :=
  unpack_pack _ _ _

theorem frobWord_iter3 (a : BitVec 192) :
    frobWord (frobWord (frobWord a)) = a := by
  rw [← pack_unpack a]
  simp only [frobWord, (unpack_pack _ _ _).1,
    (unpack_pack _ _ _).2.1, (unpack_pack _ _ _).2.2]
  congr 1
  · rw [BitVec.xor_comm (limb1 a) (limb2 a),
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · rw [← BitVec.xor_assoc (limb1 a ^^^ limb2 a) (limb2 a) (limb1 a ^^^ limb2 a),
      BitVec.xor_assoc (limb1 a) (limb2 a) (limb2 a),
      BitVec.xor_self, BitVec.xor_zero,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

private theorem base_period {R : Type*} [Field R] [Finite R]
    (a : R) (nonzero : a ≠ 0) : a ^ (Nat.card R - 1) = 1 := by
  have h := pow_card_eq_one' (x := Units.mk0 a nonzero)
  have values := congrArg (fun u : Rˣ => u.val) h
  simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
    Nat.card_units] using values

theorem base_pow_q (k : KRing) : k ^ (2^64) = k := by
  letI : Field KRing := base_isField.toField
  by_cases h : k = 0
  · rw [h, zero_pow (by decide)]
  · have p := base_period k h
    rw [← F1eResearch.quotient_card]
    have card_pos : 1 ≤ Nat.card KRing := by rw [F1eResearch.quotient_card]; decide
    calc
      k ^ Nat.card KRing = k ^ (Nat.card KRing - 1 + 1) := by congr 1; omega
      _ = k := by rw [pow_succ, p, one_mul]

theorem base_embedding_pow_q (k : BitVec 64) : base k ^ (2^64) = base k := by
  rw [base, ← map_pow, base_pow_q]

private instance : CharP ERing 2 :=
  (CharP.charP_iff_prime_eq_zero (R := ERing) (by decide)).mpr ring_numeral_two

private theorem add_self_zero (a : ERing) : a + a = 0 := by
  have h : -a = a := ZModModule.neg_eq_self _
  calc
    a + a = -a + a := congrArg (fun x => x + a) h.symm
    _ = 0 := neg_add_cancel a

theorem y_seventh : y ^ 7 = 1 := by
  calc
    y ^ 7 = y ^ 3 * y ^ 4 := by rw [← pow_add]
    _ = (y + 1) * (y ^ 2 + y) := by rw [y_cubic, y_fourth]
    _ = y ^ 3 + (y ^ 2 + y ^ 2) + y := by ring
    _ = (y + y) + 1 := by rw [y_cubic, add_self_zero, add_zero]; ac_rfl
    _ = 1 := by rw [add_self_zero, zero_add]

theorem y_pow_q : y ^ (2^64) = y ^ 2 := by
  calc
    y ^ (2^64) = y ^ ((2^64) % 7) := pow_eq_pow_mod _ y_seventh
    _ = y ^ 2 := by norm_num

theorem y_square_pow_q : (y^2) ^ (2^64) = y^4 := by
  calc
    (y^2) ^ (2^64) = (y^(2^64))^2 := by rw [←pow_mul, ←pow_mul, Nat.mul_comm]
    _ = y^4 := by rw [y_pow_q, ←pow_mul]

theorem toE_frobWord (a : BitVec 192) :
    toE (frobWord a) = (toE a) ^ (2^64) := by
  rw [frobWord, toE_pack, base_xor, toE_expansion]
  rw [add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow]
  rw [base_embedding_pow_q, base_embedding_pow_q, base_embedding_pow_q,
    y_pow_q, y_square_pow_q, y_fourth]
  ring

theorem frobWord_mul (a b : BitVec 192) :
    frobWord (Leanisa.Functions.emul a b) =
      Leanisa.Functions.emul (frobWord a) (frobWord b) := by
  apply toE_injective
  rw [toE_frobWord, toE_emul, mul_pow, toE_emul,
    toE_frobWord, toE_frobWord]

theorem frobWord_fixed_iff_base (a : BitVec 192) :
    frobWord a = a ↔ limb1 a = 0#64 ∧ limb2 a = 0#64 := by
  constructor
  · intro h
    have h1 := congrArg limb1 h
    have h2 := congrArg limb2 h
    rw [(frobWord_limbs a).2.1] at h1
    rw [(frobWord_limbs a).2.2] at h2
    rw [h1] at h2
    have mid0 : limb1 a = 0#64 := by simpa only [BitVec.xor_self] using h2.symm
    exact ⟨mid0, h1.trans mid0⟩
  · rintro ⟨h1, h2⟩
    conv_rhs => rw [← pack_unpack a]
    simp [frobWord, h1, h2]

/-- The two conjugates in the Rust source's extension inverse. -/
def mWord (a : BitVec 192) : BitVec 192 :=
  Leanisa.Functions.emul (frobWord a) (frobWord (frobWord a))

/-- The exact source-shaped norm product, including all three output limbs. -/
def normWord (a : BitVec 192) : BitVec 192 :=
  Leanisa.Functions.emul a (mWord a)

theorem normWord_fixed (a : BitVec 192) : frobWord (normWord a) = normWord a := by
  simp only [normWord, mWord, frobWord_mul, frobWord_iter3]
  rw [emul_comm (frobWord (frobWord a)) a, ← emul_assoc,
    emul_comm (frobWord a) a, emul_assoc]

theorem normWord_upper_zero (a : BitVec 192) :
    limb1 (normWord a) = 0#64 ∧ limb2 (normWord a) = 0#64 :=
  (frobWord_fixed_iff_base _).mp (normWord_fixed a)

theorem normWord_eq_embed (a : BitVec 192) :
    normWord a = Leanisa.Functions.embed_k (limb0 (normWord a)) := by
  exact (in_k_embedding _).mp ((in_k_upper_limbs _).mpr (normWord_upper_zero a))

theorem normWord_low_nonzero (a : BitVec 192) (nonzero : a ≠ 0#192) :
    limb0 (normWord a) ≠ 0#64 := by
  letI : Field ERing := extension_isField.toField
  have ha : toE a ≠ 0 := by
    intro h
    exact nonzero (toE_injective (h.trans toE_zero.symm))
  have hn : toE (normWord a) ≠ 0 := by
    simp only [normWord, mWord, toE_emul, toE_frobWord]
    exact mul_ne_zero ha (mul_ne_zero (pow_ne_zero _ ha)
      (pow_ne_zero _ (pow_ne_zero _ ha)))
  intro h0
  apply hn
  rw [normWord_eq_embed, h0, toE_embed, base_zero]

theorem normWord_zero : normWord (0#192) = 0#192 := by
  simp only [normWord, emul_zero_left]

theorem normWord_middle_basis :
    normWord (pack (0#64) (1#64) (0#64)) = 1#192 := by
  apply toE_injective
  simp only [normWord, mWord, toE_emul, toE_frobWord, middle_basis, toE_one]
  rw [y_pow_q, y_square_pow_q]
  calc
    y * (y ^ 2 * y ^ 4) = y ^ 7 := by ring
    _ = 1 := y_seventh

end Leanisa.Proofs.Extension.F1e5b
