import ExtensionInverse
import Mathlib.Data.Fintype.Units

/-! An auxiliary source-shaped base-field inverse candidate over extracted Sail `kmul`. -/

open Leanisa.Proofs.Quotient
namespace Leanisa.Proofs.BaseItoh

/-- Repeated squaring uses the actual extracted Sail multiplication. -/
def squareN (a : BitVec 64) : Nat → BitVec 64
  | 0 => a
  | n + 1 => squareN (Leanisa.Functions.kmul a a) n

def t1 (a : BitVec 64) : BitVec 64 := a
def t2 (a : BitVec 64) : BitVec 64 :=
  Leanisa.Functions.kmul (squareN (t1 a) 1) (t1 a)
def t3 (a : BitVec 64) : BitVec 64 :=
  Leanisa.Functions.kmul (squareN (t2 a) 1) (t1 a)
def t6 (a : BitVec 64) : BitVec 64 :=
  Leanisa.Functions.kmul (squareN (t3 a) 3) (t3 a)
def t7 (a : BitVec 64) : BitVec 64 :=
  Leanisa.Functions.kmul (squareN (t6 a) 1) (t1 a)
def t14 (a : BitVec 64) : BitVec 64 :=
  Leanisa.Functions.kmul (squareN (t7 a) 7) (t7 a)
def t15 (a : BitVec 64) : BitVec 64 :=
  Leanisa.Functions.kmul (squareN (t14 a) 1) (t1 a)
def t30 (a : BitVec 64) : BitVec 64 :=
  Leanisa.Functions.kmul (squareN (t15 a) 15) (t15 a)
def t31 (a : BitVec 64) : BitVec 64 :=
  Leanisa.Functions.kmul (squareN (t30 a) 1) (t1 a)
def t62 (a : BitVec 64) : BitVec 64 :=
  Leanisa.Functions.kmul (squareN (t31 a) 31) (t31 a)
def t63 (a : BitVec 64) : BitVec 64 :=
  Leanisa.Functions.kmul (squareN (t62 a) 1) (t1 a)

/-- The Rust base inverse's final square, including its zero behavior. -/
def baseItohWord (a : BitVec 64) : BitVec 64 := squareN (t63 a) 1

theorem toK_squareN (a : BitVec 64) (n : Nat) :
    toK (squareN a n) = toK a ^ (2 ^ n) := by
  induction n generalizing a with
  | zero => simp only [squareN, pow_zero, pow_one]
  | succ n ih =>
    simp only [squareN]
    rw [ih, toK_kmul, ← sq, ← pow_mul, pow_succ, mul_comm]

private theorem chain_exponent (n m : Nat) :
    (2 ^ n - 1) * 2 ^ m + (2 ^ m - 1) = 2 ^ (n + m) - 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [pow_add]
  generalize 2 ^ n = A at *
  generalize 2 ^ m = B at *
  cases A with
  | zero => omega
  | succ a =>
    cases B with
    | zero => omega
    | succ b => simp [Nat.succ_mul, Nat.mul_succ]

noncomputable def chainTarget (q : KRing) (k : Nat) : KRing := q ^ (2 ^ k - 1)

private theorem chainTarget_step {q x y : KRing} {n m : Nat}
    (hx : x = chainTarget q n) (hy : y = chainTarget q m) :
    x ^ (2 ^ m) * y = chainTarget q (n + m) := by
  rw [hx, hy, chainTarget, chainTarget, chainTarget, ← pow_mul, ← pow_add,
    chain_exponent]

theorem toK_t1 (a : BitVec 64) : toK (t1 a) = chainTarget (toK a) 1 := by
  simp [t1, chainTarget]

theorem toK_t2 (a : BitVec 64) : toK (t2 a) = chainTarget (toK a) 2 := by
  simp only [t2, toK_kmul, toK_squareN]
  simpa only [Nat.reduceAdd] using
    (chainTarget_step (toK_t1 a) (toK_t1 a))

theorem toK_t3 (a : BitVec 64) : toK (t3 a) = chainTarget (toK a) 3 := by
  simp only [t3, toK_kmul, toK_squareN]
  simpa only [Nat.reduceAdd] using
    (chainTarget_step (toK_t2 a) (toK_t1 a))

theorem toK_t6 (a : BitVec 64) : toK (t6 a) = chainTarget (toK a) 6 := by
  simp only [t6, toK_kmul, toK_squareN]
  simpa only [Nat.reduceAdd] using
    (chainTarget_step (toK_t3 a) (toK_t3 a))

theorem toK_t7 (a : BitVec 64) : toK (t7 a) = chainTarget (toK a) 7 := by
  simp only [t7, toK_kmul, toK_squareN]
  simpa only [Nat.reduceAdd] using
    (chainTarget_step (toK_t6 a) (toK_t1 a))

theorem toK_t14 (a : BitVec 64) : toK (t14 a) = chainTarget (toK a) 14 := by
  simp only [t14, toK_kmul, toK_squareN]
  simpa only [Nat.reduceAdd] using
    (chainTarget_step (toK_t7 a) (toK_t7 a))

theorem toK_t15 (a : BitVec 64) : toK (t15 a) = chainTarget (toK a) 15 := by
  simp only [t15, toK_kmul, toK_squareN]
  simpa only [Nat.reduceAdd] using
    (chainTarget_step (toK_t14 a) (toK_t1 a))

theorem toK_t30 (a : BitVec 64) : toK (t30 a) = chainTarget (toK a) 30 := by
  simp only [t30, toK_kmul, toK_squareN]
  simpa only [Nat.reduceAdd] using
    (chainTarget_step (toK_t15 a) (toK_t15 a))

theorem toK_t31 (a : BitVec 64) : toK (t31 a) = chainTarget (toK a) 31 := by
  simp only [t31, toK_kmul, toK_squareN]
  simpa only [Nat.reduceAdd] using
    (chainTarget_step (toK_t30 a) (toK_t1 a))

theorem toK_t62 (a : BitVec 64) : toK (t62 a) = chainTarget (toK a) 62 := by
  simp only [t62, toK_kmul, toK_squareN]
  simpa only [Nat.reduceAdd] using
    (chainTarget_step (toK_t31 a) (toK_t31 a))

theorem toK_t63 (a : BitVec 64) : toK (t63 a) = chainTarget (toK a) 63 := by
  simp only [t63, toK_kmul, toK_squareN]
  simpa only [Nat.reduceAdd] using
    (chainTarget_step (toK_t62 a) (toK_t1 a))

/-- The source-shaped chain has the inverse exponent for every input. -/
theorem toK_baseItohWord (a : BitVec 64) :
    toK (baseItohWord a) = toK a ^ (2 ^ 64 - 2) := by
  rw [baseItohWord, toK_squareN, toK_t63, chainTarget, ← pow_mul]
  congr 1

theorem baseItohWord_zero : baseItohWord (0#64) = 0#64 := by
  apply toK_injective
  rw [toK_baseItohWord, toK_zero]
  exact zero_pow (by decide)

private theorem finite_field_period {R : Type*} [Field R] [Finite R]
    (a : R) (nonzero : a ≠ 0) : a ^ (Nat.card R - 1) = 1 := by
  have h := pow_card_eq_one' (x := Units.mk0 a nonzero)
  have values := congrArg (fun u : Rˣ => u.val) h
  simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
    Nat.card_units] using values

/-- Nonzero words multiply by the executable chain to the literal base one. -/
theorem kmul_baseItohWord (a : BitVec 64) (nonzero : a ≠ 0#64) :
    Leanisa.Functions.kmul a (baseItohWord a) = 1#64 := by
  letI : Field KRing := base_isField.toField
  have nz : toK a ≠ 0 := by
    intro h
    exact nonzero (toK_injective (h.trans toK_zero.symm))
  apply toK_injective
  rw [toK_kmul, toK_one, toK_baseItohWord, ← pow_succ']
  have hexp : 2 ^ 64 - 2 + 1 = Nat.card KRing - 1 := by
    rw [F1eResearch.quotient_card]
    omega
  rw [hexp]
  exact finite_field_period _ nz

end Leanisa.Proofs.BaseItoh
