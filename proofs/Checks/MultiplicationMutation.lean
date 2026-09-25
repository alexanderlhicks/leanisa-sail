/- Adversarial support: an incorrect shifted-multiplicand update,
with the actual quotient and xtime held fixed. The counterexample uses
the multiplication refinement in PolynomialMultiplication. -/
import PolynomialMultiplication

noncomputable section
open Leanisa.Proofs.Quotient
namespace Leanisa.Proofs.MultiplicationMutation

/-- An intentionally incorrect update: add the shifted x rather than old x. -/
def lateAddStep (s : MulState) : MulState :=
  ⟨xtime s.multiplicand, s.multiplier >>> (1 : Nat),
    if s.multiplier.getLsbD 0 then s.accumulator ^^^ xtime s.multiplicand
    else s.accumulator⟩

theorem update_order_counterexample :
    mulInvariant (lateAddStep ⟨1, 1, 4⟩) ≠ mulInvariant ⟨1, 1, 4⟩ := by
  change toK (6#64) + toK (2#64) * toK (0#64) ≠
    toK (4#64) + toK (1#64) * toK (1#64)
  rw [toK_zero, mul_zero, add_zero, toK_one, mul_one]
  have h5 : toK (4#64) + 1 = toK (5#64) := by
    rw [← toK_one, ← toK_xor]
    rfl
  rw [h5]
  intro eq
  have wrong : (6#64) = 5 := toK_injective eq
  exact (by decide : (6#64) ≠ 5) wrong

theorem no_universal_mutated_invariant :
    ¬ (∀ s : MulState, mulInvariant (lateAddStep s) = mulInvariant s) := by
  intro h
  exact update_order_counterexample (h ⟨1, 1, 4⟩)

end Leanisa.Proofs.MultiplicationMutation

