import Leanisa

namespace Leanisa.Proofs
open Sail Leanisa.Functions

/-- The base-word representation, with no field structure asserted. -/
abbrev KBits := BitVec 64

/-- One logical shift and reduction, using the original high bit as carry. -/
def xtime (x : KBits) : KBits :=
  (x <<< (1 : Nat)) ^^^ (if x.getLsbD 63 then 0x1b else 0)

/-- All three multiplication registers, including an arbitrary accumulator. -/
structure MulState where
  multiplicand : KBits
  multiplier : KBits
  accumulator : KBits
  deriving DecidableEq, Repr

/-- Observe the old multiplier bit and multiplicand before shifting either. -/
def mulStep (s : MulState) : MulState :=
  ⟨xtime s.multiplicand, s.multiplier >>> (1 : Nat),
    if s.multiplier.getLsbD 0 then s.accumulator ^^^ s.multiplicand else s.accumulator⟩

/-- Structural iteration, suitable for later kernel-reduced certificates. -/
def mulIter : Nat → MulState → MulState
  | 0, s => s
  | n + 1, s => mulIter n (mulStep s)

/-- Normalized evaluator for Sail multiplication; polynomial refinement is separate. -/
def mulRef (a b : KBits) : KBits := (mulIter 64 ⟨a, b, 0⟩).accumulator

private theorem access_one (x : KBits) (i : Nat) (hi : i < 64) :
    ((Sail.BitVec.access x i) == 1#1) = x.getLsbD i := by
  simp only [Sail.BitVec.access, getElem!_pos x i hi, ← BitVec.getLsbD_eq_getElem]
  cases x.getLsbD i <;> rfl

private theorem left_shift (x : KBits) :
    Sail.BitVec.extractLsb x 62 0 +++ 0#1 = x <<< (1 : Nat) := by
  exact (BitVec.shiftLeft_eq_concat_of_lt (x := x) (n := 1) (by decide)).symm

private theorem right_shift (x : KBits) :
    0#1 +++ Sail.BitVec.extractLsb x 63 1 = x >>> (1 : Nat) := by
  exact (BitVec.ushiftRight_eq_extractLsb'_of_lt (x := x) (n := 1) (by decide)).symm

/-- The actual extracted address advance agrees with shift/reduction. -/
theorem sail_advance_eq_xtime (x : KBits) : advance x = xtime x := by
  simp only [advance, left_shift, access_one x 63 (by decide), xtime]
  cases x.getLsbD 63 <;> simp

private def mulRange : IntRange := { start := 0, stop := 63 }

def MulState.toTuple (s : MulState) : KBits × KBits × KBits :=
  (s.multiplicand, s.multiplier, s.accumulator)

/-- A source-shaped copy of the multiplication body, retaining update order.
Only the observable accumulator is linked to imported `kmul` below; hidden
final multiplicand/multiplier values are not part of that result theorem. -/
private def mulBody (i : Int) (_ : i ∈ mulRange) (state : KBits × KBits × KBits) :
    Id (ForInStep (KBits × KBits × KBits)) :=
  let (x, y, z) := state
  let z := if Sail.BitVec.access y 0 == 1#1 then z ^^^ x else z
  let carry := Sail.BitVec.access x 63
  let x := Sail.BitVec.extractLsb x 62 0 +++ 0#1
  let x := if carry == 1#1 then x ^^^ 0x1b else x
  let y := 0#1 +++ Sail.BitVec.extractLsb y 63 1
  pure (.yield (x, y, z))

private theorem body_step (i : Int) (hi : i ∈ mulRange) (s : MulState) :
    mulBody i hi s.toTuple = pure (.yield (mulStep s).toTuple) := by
  simp only [mulBody, MulState.toTuple, mulStep, left_shift, right_shift,
    access_one s.multiplier 0 (by decide), access_one s.multiplicand 63 (by decide), xtime]
  cases s.multiplicand.getLsbD 63 <;> simp

private theorem mul_loop_eq (j : Nat) (hj : j ≤ 64) (s : MulState)
    (hs : ((j : Int) - mulRange.start) % mulRange.step = 0) :
    IntRange.forIn'.loop (m := Id) mulRange mulBody s.toTuple (j : Int) hs =
      pure (mulIter (64 - j) s).toTuple := by
  rw [IntRange.forIn'.loop]
  by_cases inside : j < 64
  · have hin : (j : Int) ∈ mulRange := by simp [mulRange, Membership.mem]; omega
    simp only [dif_pos hin, body_step, pure_bind]
    have count : 64 - j = (64 - (j + 1)) + 1 := by omega
    rw [count, mulIter]
    exact mul_loop_eq (j + 1) (by omega) (mulStep s) _
  · have hout : (j : Int) ∉ mulRange := by simp [mulRange, Membership.mem]; omega
    have count : 64 - j = 0 := by omega
    simp only [dif_neg hout, count, mulIter]
termination_by 64 - j

/-- Auxiliary inclusive loop over the copied source-shaped body, started at
an arbitrary suffix index with all three registers supplied. This is not an
exposed full-state result of the extracted `kmul` function. -/
def sourceMulTail (j : Nat) (s : MulState) : MulState :=
  let result := Id.run (IntRange.forIn'.loop (m := Id) mulRange mulBody s.toTuple
    (j : Int) (by simp [mulRange]))
  ⟨result.1, result.2.1, result.2.2⟩

/-- Every auxiliary source-shaped suffix j..63 agrees in all registers with
exactly 64-j structural steps; j=64 is empty, and the accumulator is arbitrary. -/
theorem source_mul_tail_eq (j : Nat) (hj : j ≤ 64) (s : MulState) :
    sourceMulTail j s = mulIter (64 - j) s := by
  exact congrArg (fun result : KBits × KBits × KBits =>
    MulState.mk result.1 result.2.1 result.2.2)
    (mul_loop_eq j hj s (by simp [mulRange]))

/-- Universal equality with the actual Sail function. No multiplication laws
or polynomial/field representation are premises or conclusions here. -/
theorem sail_kmul_eq_mulRef (a b : KBits) : kmul a b = mulRef a b := by
  change (sourceMulTail 0 ⟨a, b, 0⟩).accumulator = mulRef a b
  rw [source_mul_tail_eq 0 (by decide)]
  rfl

end Leanisa.Proofs

#print axioms Leanisa.Proofs.sail_advance_eq_xtime

#print axioms Leanisa.Proofs.source_mul_tail_eq
#print axioms Leanisa.Proofs.sail_kmul_eq_mulRef
