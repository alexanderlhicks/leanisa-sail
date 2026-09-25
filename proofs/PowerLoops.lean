import FieldLoops

namespace Leanisa.Proofs
open Sail Leanisa.Functions

/-- Reference exponentiation registers. No ring-power meaning is asserted. -/
structure PowState where
  base : KBits
  exponent : KBits
  accumulator : KBits
  deriving DecidableEq, Repr

/-- Exact Sail order: multiply the old accumulator by the old base when the
old exponent's low bit is set, square that base, then shift the exponent. -/
def powStep (s : PowState) : PowState :=
  ⟨mulRef s.base s.base, s.exponent >>> (1 : Nat),
    if s.exponent.getLsbD 0 then mulRef s.accumulator s.base else s.accumulator⟩

def powIter : Nat → PowState → PowState
  | 0, s => s
  | n + 1, s => powIter n (powStep s)

/-- The exact-order structural evaluator for the extracted gpow result. -/
def powRef (n : KBits) : KBits := (powIter 64 ⟨2, n, 1⟩).accumulator

private theorem access_one (x : KBits) (i : Nat) (hi : i < 64) :
    ((Sail.BitVec.access x i) == 1#1) = x.getLsbD i := by
  simp only [Sail.BitVec.access, getElem!_pos x i hi, ← BitVec.getLsbD_eq_getElem]
  cases x.getLsbD i <;> rfl

private theorem right_shift (x : KBits) :
    0#1 +++ Sail.BitVec.extractLsb x 63 1 = x >>> (1 : Nat) := by
  exact (BitVec.ushiftRight_eq_extractLsb'_of_lt (x := x) (n := 1) (by decide)).symm

private def powRange : IntRange := { start := 0, stop := 63 }

def PowState.toTuple (s : PowState) : KBits × KBits × KBits :=
  (s.base, s.exponent, s.accumulator)

/-- Auxiliary copy of the source-shaped exponentiation body. Its full state
belongs to this reference interface; actual gpow exposes only an accumulator. -/
private def powBody (i : Int) (_ : i ∈ powRange) (state : KBits × KBits × KBits) :
    Id (ForInStep (KBits × KBits × KBits)) :=
  let (x, y, z) := state
  let z := if Sail.BitVec.access y 0 == 1#1 then kmul z x else z
  let x := kmul x x
  let y := 0#1 +++ Sail.BitVec.extractLsb y 63 1
  pure (.yield (x, y, z))

private theorem body_step (i : Int) (hi : i ∈ powRange) (s : PowState) :
    powBody i hi s.toTuple = pure (.yield (powStep s).toTuple) := by
  simp only [powBody, PowState.toTuple, powStep, right_shift,
    access_one s.exponent 0 (by decide), sail_kmul_eq_mulRef]

private theorem pow_loop_eq (j : Nat) (hj : j ≤ 64) (s : PowState)
    (hs : ((j : Int) - powRange.start) % powRange.step = 0) :
    IntRange.forIn'.loop (m := Id) powRange powBody s.toTuple (j : Int) hs =
      pure (powIter (64 - j) s).toTuple := by
  rw [IntRange.forIn'.loop]
  by_cases inside : j < 64
  · have hin : (j : Int) ∈ powRange := by simp [powRange, Membership.mem]; omega
    simp only [dif_pos hin, body_step, pure_bind]
    have count : 64 - j = (64 - (j + 1)) + 1 := by omega
    rw [count, powIter]
    exact pow_loop_eq (j + 1) (by omega) (powStep s) _
  · have hout : (j : Int) ∉ powRange := by simp [powRange, Membership.mem]; omega
    have count : 64 - j = 0 := by omega
    simp only [dif_neg hout, count, powIter]
termination_by 64 - j

/-- Auxiliary inclusive suffix of the copied body for arbitrary reference
registers. This is not a public hidden-state output of the extracted gpow. -/
def sourcePowTail (j : Nat) (s : PowState) : PowState :=
  let result := Id.run (IntRange.forIn'.loop (m := Id) powRange powBody s.toTuple
    (j : Int) (by simp [powRange]))
  ⟨result.1, result.2.1, result.2.2⟩

theorem source_pow_tail_eq (j : Nat) (hj : j ≤ 64) (s : PowState) :
    sourcePowTail j s = powIter (64 - j) s := by
  exact congrArg (fun result : KBits × KBits × KBits =>
    PowState.mk result.1 result.2.1 result.2.2)
    (pow_loop_eq j hj s (by simp [powRange]))

/-- Actual extracted result refinement, using accepted multiplication
normalization and preserving operand order and association exactly. -/
theorem sail_gpow_eq_powRef (n : KBits) : gpow n = powRef n := by
  simp only [gpow, pure_bind, bind_pure, ForIn.forIn, ForIn'.forIn', IntRange.forIn']
  have body : (fun (i : Int) (_ : i ∈ powRange) (r : KBits × KBits × KBits) =>
      pure (ForInStep.yield
        (kmul r.1 r.1, 0#1 +++ Sail.BitVec.extractLsb r.2.1 63 1,
          if Sail.BitVec.access r.2.1 0 == 1#1 then kmul r.2.2 r.1 else r.2.2))) = powBody := by
    funext i hi r
    rfl
  have replacement := congrArg
    (fun loopBody : (i : Int) → i ∈ powRange →
        (KBits × KBits × KBits) → Id (ForInStep (KBits × KBits × KBits)) =>
      Id.run (do
        let state ← IntRange.forIn'.loop (m := Id) powRange loopBody
          (2, n, 1) (0 : Int) (by simp [powRange])
        pure state.2.2)) body
  exact replacement.trans (congrArg (fun result : Id (KBits × KBits × KBits) => Id.run (do
    let state ← result
    pure state.2.2)) (pow_loop_eq 0 (by decide) ⟨2, n, 1⟩ (by simp [powRange])))

theorem powIter_zero_exponent (count : Nat) (base accumulator : KBits) :
    (powIter count ⟨base, 0, accumulator⟩).accumulator = accumulator := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih => simpa [powIter, powStep] using ih (mulRef base base)

/-- Origin alone; recurrence and addition laws remain separate obligations. -/
theorem sail_gpow_zero : gpow 0 = 1 := by
  rw [sail_gpow_eq_powRef]
  exact powIter_zero_exponent 64 2 1

end Leanisa.Proofs

#print axioms Leanisa.Proofs.source_pow_tail_eq
#print axioms Leanisa.Proofs.sail_gpow_eq_powRef
#print axioms Leanisa.Proofs.sail_gpow_zero
