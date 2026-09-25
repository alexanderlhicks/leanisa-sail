/- Adversarial support: using the squared base for accumulation violates
the old-state dependency proved in PolynomialExponentiation. -/
import PolynomialExponentiation

noncomputable section
open Leanisa.Proofs.Quotient
namespace Leanisa.Proofs.ExponentiationMutation

def squareFirst (s : PowState) : PowState :=
  ⟨mulRef s.base s.base, s.exponent >>> (1 : Nat),
    if s.exponent.getLsbD 0 then mulRef s.accumulator (mulRef s.base s.base)
    else s.accumulator⟩

set_option maxRecDepth 10000 in
theorem square_first_counterexample :
    powInvariant (squareFirst ⟨2,1,3⟩) ≠ powInvariant ⟨2,1,3⟩ := by
  change toK (12#64) * toK (4#64) ^ 0 ≠ toK (3#64) * toK (2#64) ^ 1
  rw [pow_zero, mul_one, pow_one, ← toK_mulRef]
  change toK (12#64) ≠ toK (6#64)
  intro eq
  exact (by decide : (12#64) ≠ 6) (toK_injective eq)

theorem no_universal_square_first_invariant :
    ¬ (∀ s : PowState, powInvariant (squareFirst s) = powInvariant s) := by
  intro h
  exact square_first_counterexample (h ⟨2, 1, 3⟩)

end Leanisa.Proofs.ExponentiationMutation

