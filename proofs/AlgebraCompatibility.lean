import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.GroupTheory.OrderOfElement
import Leanisa

/-! Dependency compatibility only: quotient/ring interfaces and a conditional
order-certificate specialization coexist with the actual Sail extraction. No
field property, generator order, or arithmetic refinement is claimed. -/
noncomputable section

namespace Leanisa.Proofs.AlgebraCompatibility

def modulus : Polynomial (ZMod 2) :=
  Polynomial.X^64 + Polynomial.X^4 + Polynomial.X^3 + Polynomial.X + 1

abbrev KRing := AdjoinRoot modulus
def generator : KRing := AdjoinRoot.root modulus

example : CommRing KRing := inferInstance

theorem quotient_relation : AdjoinRoot.mk modulus modulus = 0 :=
  AdjoinRoot.mk_self (f := modulus)

theorem ring_associativity (a b c : KRing) : (a * b) * c = a * (b * c) :=
  mul_assoc a b c

theorem conditional_order_certificate (n : Nat) (positive : 0 < n)
    (period : generator ^ n = 1)
    (factors : ∀ p : Nat, p.Prime → p ∣ n → generator ^ (n / p) ≠ 1) :
    orderOf generator = n :=
  orderOf_eq_of_pow_and_pow_div_prime positive period factors

theorem extracted_embedding (x : BitVec 64) :
    Leanisa.Functions.in_k (Leanisa.Functions.embed_k x) = true := by
  simp only [Leanisa.Functions.in_k, Leanisa.Functions.embed_k,
    Sail.BitVec.extractLsb, beq_iff_eq]
  exact BitVec.extractLsb'_append_eq_left

end Leanisa.Proofs.AlgebraCompatibility

#print axioms Leanisa.Proofs.AlgebraCompatibility.quotient_relation
#print axioms Leanisa.Proofs.AlgebraCompatibility.ring_associativity
#print axioms Leanisa.Proofs.AlgebraCompatibility.conditional_order_certificate
#print axioms Leanisa.Proofs.AlgebraCompatibility.extracted_embedding
