import QuotientRepresentation

/-
Three-limb extension representation over the binary polynomial quotient.
The cubic is X^3 + X + 1; no irreducibility, field, cancellation, or inverse
assumptions are used in the representation lemmas.
-/

noncomputable section
open Polynomial Leanisa.Proofs.Quotient
namespace Leanisa.Proofs.Extension

instance kNontrivial : Nontrivial KRing :=
  nontrivial_of_ne (toK (0#64)) (toK (1#64)) (fun h => by
    have bad := toK_injective h
    exact (by decide : (0#64) ≠ 1#64) bad)

def limb0 (a : BitVec 192) : BitVec 64 := Sail.BitVec.extractLsb a 63 0
def limb1 (a : BitVec 192) : BitVec 64 := Sail.BitVec.extractLsb a 127 64
def limb2 (a : BitVec 192) : BitVec 64 := Sail.BitVec.extractLsb a 191 128
def pack (lo mid hi : BitVec 64) : BitVec 192 := hi ++ (mid ++ lo)

theorem unpack_pack (lo mid hi : BitVec 64) :
    limb0 (pack lo mid hi) = lo ∧ limb1 (pack lo mid hi) = mid ∧
    limb2 (pack lo mid hi) = hi := by
  simp only [limb0, limb1, limb2, pack, Sail.BitVec.extractLsb, BitVec.extractLsb]
  constructor
  · rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 128)]
    exact BitVec.extractLsb'_append_eq_right
  constructor
  · rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 64 + 64 ≤ 128)]
    exact BitVec.extractLsb'_append_eq_left
  · exact BitVec.extractLsb'_append_eq_left

theorem pack_unpack (a : BitVec 192) : pack (limb0 a) (limb1 a) (limb2 a) = a := by
  simp only [pack, limb0, limb1, limb2, Sail.BitVec.extractLsb, BitVec.extractLsb]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_append_extractLsb'

theorem limb_xor (a b : BitVec 192) :
    limb0 (a ^^^ b) = limb0 a ^^^ limb0 b ∧
    limb1 (a ^^^ b) = limb1 a ^^^ limb1 b ∧
    limb2 (a ^^^ b) = limb2 a ^^^ limb2 b := by
  simp [limb0, limb1, limb2, Sail.BitVec.extractLsb, BitVec.extractLsb_xor]

def wordPoly (a : BitVec 192) : Polynomial KRing :=
  C (toK (limb0 a)) + C (toK (limb1 a)) * X + C (toK (limb2 a)) * X^2

theorem wordPoly_coeff (a : BitVec 192) (i : Nat) :
    (wordPoly a).coeff i = if i = 0 then toK (limb0 a)
      else if i = 1 then toK (limb1 a) else if i = 2 then toK (limb2 a) else 0 := by
  by_cases h0 : i = 0
  · subst i; simp [wordPoly]
  by_cases h1 : i = 1
  · subst i; simp [wordPoly]
  by_cases h2 : i = 2
  · subst i; simp [wordPoly]
  simp [wordPoly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
    h0, h1, h2, Ne.symm h1]

theorem wordPoly_degree_lt (a : BitVec 192) : (wordPoly a).degree < 3 := by
  apply (degree_lt_iff_coeff_zero _ 3).mpr
  intro i hi
  rw [wordPoly_coeff]
  simp [show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega]

theorem wordPoly_injective : Function.Injective wordPoly := by
  intro a b h
  have h0 := congrArg (fun p : Polynomial KRing => p.coeff 0) h
  have h1 := congrArg (fun p : Polynomial KRing => p.coeff 1) h
  have h2 := congrArg (fun p : Polynomial KRing => p.coeff 2) h
  simp only [wordPoly_coeff] at h0 h1 h2
  have e0 : limb0 a = limb0 b := toK_injective (by simpa using h0)
  have e1 : limb1 a = limb1 b := toK_injective (by simpa using h1)
  have e2 : limb2 a = limb2 b := toK_injective (by simpa using h2)
  rw [← pack_unpack a, e0, e1, e2, pack_unpack]

def cubic : Polynomial KRing := X^3 + (X + 1)

theorem cubic_low_degree : (X + 1 : Polynomial KRing).degree < 3 := by
  apply (degree_lt_iff_coeff_zero _ 3).mpr
  intro i hi
  simp [coeff_add, coeff_X, coeff_one, show 1 ≠ i by omega, show i ≠ 0 by omega]

theorem cubic_monic : cubic.Monic := monic_X_pow_add cubic_low_degree

theorem cubic_degree : cubic.degree = 3 := by
  have h : (X + 1 : Polynomial KRing).degree < (X^3 : Polynomial KRing).degree := by
    simpa only [degree_X_pow] using cubic_low_degree
  simpa only [cubic, degree_X_pow] using degree_add_eq_left_of_degree_lt h

theorem cubic_natDegree : cubic.natDegree = 3 := by
  have h : cubic.degree = (X^3 : Polynomial KRing).degree := by
    simpa only [degree_X_pow] using cubic_degree
  simpa only [natDegree_X_pow] using natDegree_eq_of_degree_eq h

abbrev ERing := AdjoinRoot cubic
def toE (a : BitVec 192) : ERing := AdjoinRoot.mk cubic (wordPoly a)
def base (a : BitVec 64) : ERing := AdjoinRoot.of cubic (toK a)
def y : ERing := AdjoinRoot.root cubic

theorem toE_injective : Function.Injective toE := by
  intro a b h
  apply wordPoly_injective
  by_contra hne
  have hnz : wordPoly a - wordPoly b ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (wordPoly a - wordPoly b).degree < cubic.degree := by
    rw [cubic_degree]
    exact (degree_sub_le _ _).trans_lt (max_lt (wordPoly_degree_lt a) (wordPoly_degree_lt b))
  exact (cubic_monic.not_dvd_of_degree_lt hnz hdeg) (AdjoinRoot.mk_eq_mk.mp h)

theorem toE_expansion (a : BitVec 192) :
    toE a = base (limb0 a) + base (limb1 a) * y + base (limb2 a) * y^2 := by
  simp only [toE, wordPoly, base, y, map_add, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]

theorem y_cubic : y^3 = y + 1 := by
  have h := AdjoinRoot.mk_self (f := cubic)
  change AdjoinRoot.mk cubic (X^3 + (X + 1)) = 0 at h
  simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X] at h
  have h' := eq_neg_of_add_eq_zero_left h
  simpa only [y, ZModModule.neg_eq_self] using h'

theorem y_fourth : y^4 = y^2 + y := by
  rw [show 4 = 3 + 1 by decide, pow_succ, y_cubic, add_mul, one_mul, ← pow_two]


theorem base_zero : base (0#64) = 0 := by simp only [base, toK_zero, map_zero]
theorem base_one : base (1#64) = 1 := by simp only [base, toK_one, map_one]
theorem base_xor (a b : BitVec 64) : base (a ^^^ b) = base a + base b := by
  simp only [base, toK_xor, map_add]
theorem toE_pack (lo mid hi : BitVec 64) :
    toE (pack lo mid hi) = base lo + base mid * y + base hi * y^2 := by
  rw [toE_expansion, (unpack_pack lo mid hi).1,
    (unpack_pack lo mid hi).2.1, (unpack_pack lo mid hi).2.2]

theorem toE_xor (a b : BitVec 192) : toE (a ^^^ b) = toE a + toE b := by
  simp only [toE_expansion, (limb_xor a b).1, (limb_xor a b).2.1,
    (limb_xor a b).2.2, base_xor, add_mul]
  ac_rfl

theorem embed_packing (a : BitVec 64) : Leanisa.Functions.embed_k a = pack a (0#64) (0#64) := by
  change (0#128) ++ a = (0#64) ++ ((0#64) ++ a)
  have h : (0#64) ++ (0#64) = 0#128 := by decide
  simpa only [h, BitVec.cast_eq] using
    (BitVec.append_assoc (x₁ := 0#64) (x₂ := 0#64) (x₃ := a))

theorem toE_embed (a : BitVec 64) : toE (Leanisa.Functions.embed_k a) = base a := by
  rw [embed_packing, toE_pack, base_zero]
  simp only [zero_mul, add_zero]

theorem middle_basis : toE (pack (0#64) (1#64) (0#64)) = y := by
  rw [toE_pack, base_zero, base_one]
  simp

theorem high_basis : toE (pack (0#64) (0#64) (1#64)) = y^2 := by
  rw [toE_pack, base_zero, base_one]
  simp


theorem toE_zero : toE (0#192) = 0 := by
  have h : (0#192) = pack (0#64) (0#64) (0#64) := by decide
  rw [h, toE_pack, base_zero]
  simp

theorem toE_one : toE (1#192) = 1 := by
  have h : (1#192) = pack (1#64) (0#64) (0#64) := by decide
  rw [h, toE_pack, base_zero, base_one]
  simp

instance eNontrivial : Nontrivial ERing :=
  nontrivial_of_ne (toE (0#192)) (toE (1#192)) (fun h => by
    have bad := toE_injective h
    exact (by decide : (0#192) ≠ 1#192) bad)

theorem constant_basis : toE (pack (1#64) (0#64) (0#64)) = 1 := by
  rw [toE_pack, base_zero, base_one]
  simp

theorem base_word_two : base (2#64) = AdjoinRoot.of cubic (AdjoinRoot.root modulus) := by
  simp only [base, toK_two]

theorem ring_numeral_two : (2 : ERing) = 0 := by
  have negone : -(1 : ERing) = 1 := ZModModule.neg_eq_self _
  calc
    (2 : ERing) = 1 + 1 := (one_add_one_eq_two).symm
    _ = -(1 : ERing) + 1 := by rw [negone]
    _ = 0 := neg_add_cancel _

theorem in_k_embedding (a : BitVec 192) :
    Leanisa.Functions.in_k a = true ↔ a = Leanisa.Functions.embed_k (limb0 a) := by
  constructor
  · intro accepted
    have upper : a.extractLsb' 64 128 = 0#128 := by
      simpa only [Leanisa.Functions.in_k, Sail.BitVec.extractLsb, BitVec.extractLsb, beq_iff_eq] using accepted
    have assembled := BitVec.extractLsb'_append_extractLsb' (x := a) (w := 128) (len := 64)
    rw [upper] at assembled
    exact assembled.symm
  · intro equals
    rw [equals]
    simp only [Leanisa.Functions.in_k, Leanisa.Functions.embed_k, Sail.BitVec.extractLsb, BitVec.extractLsb,
      BitVec.extractLsb'_append_eq_left, beq_self_eq_true]

theorem in_k_upper_limbs (a : BitVec 192) :
    Leanisa.Functions.in_k a = true ↔ limb1 a = 0#64 ∧ limb2 a = 0#64 := by
  constructor
  · intro accepted
    have repr := (in_k_embedding a).mp accepted
    have slices := (unpack_pack (limb0 a) (0#64) (0#64)).2
    rw [← embed_packing, ← repr] at slices
    exact slices
  · rintro ⟨mid, high⟩
    apply (in_k_embedding a).mpr
    calc
      a = pack (limb0 a) (limb1 a) (limb2 a) := (pack_unpack a).symm
      _ = pack (limb0 a) (0#64) (0#64) := by rw [mid, high]
      _ = Leanisa.Functions.embed_k (limb0 a) := (embed_packing _).symm


end Leanisa.Proofs.Extension
