import Runner

namespace Leanisa.Proofs
open Sail Leanisa.Functions

/-- A successful product relation gives the complete extracted Sail MUL result. -/
theorem step_mul_of_reads {n : Nat} (mem : Vector Word n) (s : machine_state)
    (oa ob oc : BitVec 64) (va vb : Word)
    (ra : read_memory mem (kmul s.fp oa) = ⟨va, true⟩)
    (rb : read_memory mem (kmul s.fp ob) = ⟨vb, true⟩)
    (rc : read_memory mem (kmul s.fp oc) = ⟨emul va vb, true⟩) :
    step s (.Mul (oa, ob, oc)) mem = ⟨advancedState s, .Running⟩ := by
  simp only [step, step_indexed, read_memory_indexed_empty, ra, rb, rc]
  simp [advancedState, show (status.Running == status.Running) = true from rfl]

/-- Observe both operands, then assign their extracted Sail product consistently.
Inputs and output can alias: each eager observation is fixed before the assignment. -/
def mulAssign {n : Nat} (memory : PartialMemory n) (a b c : Fin n) :
    Option (PartialMemory n) :=
  let first := observeZero memory a
  let second := observeZero first.2 b
  assign second.2 c (emul first.1 second.1)

theorem mulAssign_evolves {n : Nat} {memory next : PartialMemory n} (a b c : Fin n)
    (assigned : mulAssign memory a b c = some next) : Evolves memory next := by
  exact .trans (.observation memory a)
    (.trans (.observation (observeZero memory a).2 b) (.assignment c _ assigned))

/-- Preservation of the observed operands and product gives a concrete MUL step.
The multiplication is the Sail definition itself; no Rust arithmetic theorem is assumed. -/
theorem mul_policy_simulates_step {n : Nat} (mem : Vector Word n) (domain : GPowerDomain n)
    (s : machine_state) (oa ob oc : BitVec 64) (a b c : Fin n)
    {memory next later : PartialMemory n}
    (maps_a : kmul s.fp oa = gAddress a.val)
    (maps_b : kmul s.fp ob = gAddress b.val)
    (maps_c : kmul s.fp oc = gAddress c.val)
    (assigned : mulAssign memory a b c = some next)
    (execution : Evolves next later)
    (finished : Completes later (vectorImage mem)) :
    step s (.Mul (oa, ob, oc)) mem = ⟨advancedState s, .Running⟩ := by
  let first := observeZero memory a
  let second := observeZero first.2 b
  have write : assign second.2 c (emul first.1 second.1) = some next := assigned
  have second_later : Extends second.2 later :=
    extends_trans (assign_extends write) (execution_extends execution)
  have first_later : Extends first.2 later :=
    extends_trans (observe_extends first.2 b) second_later
  apply step_mul_of_reads mem s oa ob oc first.1 second.1
  · exact completed_cell_lookup mem domain finished a first.1
      (first_later a first.1 (observe_fixes_value memory a)) _ maps_a
  · exact completed_cell_lookup mem domain finished b second.1
      (second_later b second.1 (observe_fixes_value first.2 b)) _ maps_b
  · exact completed_cell_lookup mem domain finished c (emul first.1 second.1)
      (execution_extends execution c _ (assign_fixes_value write)) _ maps_c

/-- Supply a candidate for a missing operand before eagerly observing it.
The advice is checked for write consistency, then the product is checked too.
This does not assert that an inverse-based solver returns a valid candidate. -/
def mulAssignWithAdvice {n : Nat} (memory : PartialMemory n)
    (hint : Fin n) (value : Word) (a b c : Fin n) : Option (PartialMemory n) :=
  (assign memory hint value).bind fun prepared => mulAssign prepared a b c

theorem mul_advice_decomposes {n : Nat} {memory next : PartialMemory n}
    (hint : Fin n) (value : Word) (a b c : Fin n)
    (assigned : mulAssignWithAdvice memory hint value a b c = some next) :
    ∃ prepared, assign memory hint value = some prepared ∧
      mulAssign prepared a b c = some next := by
  unfold mulAssignWithAdvice at assigned
  cases advice : assign memory hint value with
  | none => simp [advice] at assigned
  | some prepared => exact ⟨prepared, rfl, by simpa [advice] using assigned⟩

theorem mulAssignWithAdvice_evolves {n : Nat} {memory next : PartialMemory n}
    (hint : Fin n) (value : Word) (a b c : Fin n)
    (assigned : mulAssignWithAdvice memory hint value a b c = some next) :
    Evolves memory next := by
  obtain ⟨prepared, advice, product⟩ := mul_advice_decomposes hint value a b c assigned
  exact .trans (.assignment hint value advice) (mulAssign_evolves a b c product)

theorem mul_advice_simulates_step {n : Nat} (mem : Vector Word n) (domain : GPowerDomain n)
    (s : machine_state) (oa ob oc : BitVec 64) (a b c hint : Fin n) (value : Word)
    {memory next later : PartialMemory n}
    (maps_a : kmul s.fp oa = gAddress a.val)
    (maps_b : kmul s.fp ob = gAddress b.val)
    (maps_c : kmul s.fp oc = gAddress c.val)
    (assigned : mulAssignWithAdvice memory hint value a b c = some next)
    (execution : Evolves next later)
    (finished : Completes later (vectorImage mem)) :
    step s (.Mul (oa, ob, oc)) mem = ⟨advancedState s, .Running⟩ := by
  obtain ⟨prepared, advice, product⟩ := mul_advice_decomposes hint value a b c assigned
  exact mul_policy_simulates_step mem domain s oa ob oc a b c maps_a maps_b maps_c
    product execution finished

/-- Checked advice can never change an earlier eager observation. -/
theorem mul_advice_rejects_changed_observation {n : Nat} (memory : PartialMemory n)
    (hint a b c : Fin n) (value : Word)
    (different : value ≠ (observeZero memory hint).1) :
    mulAssignWithAdvice (observeZero memory hint).2 hint value a b c = none := by
  simp [mulAssignWithAdvice, rejects_changed_observation memory hint value different]

/-- A fully aliased MUL succeeds exactly when its observed word is idempotent.
This is a conditional bitvector fact, not an assumption that the field laws hold. -/
theorem mul_all_alias_known {n : Nat} (memory : PartialMemory n) (a : Fin n) (v : Word)
    (fixed : memory a = some v) :
    mulAssign memory a a a = if emul v v = v then some memory else none := by
  simp [mulAssign, observeZero, fixed, assign, eq_comm]

/-- A multiplication with a preassigned output succeeds only if it agrees with
that output, including when an output aliases either observed input. -/
theorem mul_preserves_known_output {n : Nat} {memory next : PartialMemory n}
    (a b c : Fin n) (v : Word) (fixed : memory c = some v)
    (assigned : mulAssign memory a b c = some next) :
    emul (observeZero memory a).1 (observeZero (observeZero memory a).2 b).1 = v := by
  have old := execution_extends (mulAssign_evolves a b c assigned) c v fixed
  have product := assign_fixes_value assigned
  exact Option.some.inj (product.symm.trans old)

/-- SET and XOR retain their existing policy; MUL adds forward or checked-advice
execution. All effective-address equations are explicit and indices may alias. -/
inductive ArithmeticStep {m : Nat} (s : machine_state) :
    PartialMemory m → instruction → PartialMemory m → Prop where
  | setXor {before after ins} (operation : SetXorStep s before ins after) :
      ArithmeticStep s before ins after
  | mul {before after} (oa ob oc : BitVec 64) (a b c : Fin m)
      (maps_a : kmul s.fp oa = gAddress a.val)
      (maps_b : kmul s.fp ob = gAddress b.val)
      (maps_c : kmul s.fp oc = gAddress c.val)
      (assigned : mulAssign before a b c = some after) :
      ArithmeticStep s before (.Mul (oa, ob, oc)) after
  | mulAdvice {before after} (oa ob oc : BitVec 64) (a b c hint : Fin m) (value : Word)
      (maps_a : kmul s.fp oa = gAddress a.val)
      (maps_b : kmul s.fp ob = gAddress b.val)
      (maps_c : kmul s.fp oc = gAddress c.val)
      (assigned : mulAssignWithAdvice before hint value a b c = some after) :
      ArithmeticStep s before (.Mul (oa, ob, oc)) after

theorem ArithmeticStep.evolves {m : Nat} {s : machine_state}
    {before after : PartialMemory m} {ins : instruction}
    (operation : ArithmeticStep s before ins after) : Evolves before after := by
  cases operation with
  | setXor operation => exact operation.evolves
  | mul oa ob oc a b c maps_a maps_b maps_c assigned => exact mulAssign_evolves a b c assigned
  | mulAdvice oa ob oc a b c hint value maps_a maps_b maps_c assigned =>
    exact mulAssignWithAdvice_evolves hint value a b c assigned

theorem ArithmeticStep.simulates {m : Nat} (mem : Vector Word m) (domain : GPowerDomain m)
    {s : machine_state} {before after later : PartialMemory m} {ins : instruction}
    (operation : ArithmeticStep s before ins after) (continuation : Evolves after later)
    (finished : Completes later (vectorImage mem)) :
    step s ins mem = ⟨advancedState s, .Running⟩ := by
  cases operation with
  | setXor operation => exact operation.simulates mem domain continuation finished
  | mul oa ob oc a b c maps_a maps_b maps_c assigned =>
    exact mul_policy_simulates_step mem domain s oa ob oc a b c maps_a maps_b maps_c
      assigned continuation finished
  | mulAdvice oa ob oc a b c hint value maps_a maps_b maps_c assigned =>
    exact mul_advice_simulates_step mem domain s oa ob oc a b c hint value maps_a maps_b maps_c
      assigned continuation finished

/-- Every instruction before the sentinel uses a compatible arithmetic policy. -/
def ArithmeticFragment {p m : Nat} (program : Vector instruction p)
    (memories : Nat → PartialMemory m) : Prop :=
  ∀ i (hi : i < p - 1), ArithmeticStep (registersAt i) (memories i)
    (program.get ⟨i, by omega⟩) (memories (i + 1))

theorem SetXorFragment.to_arithmetic {p m : Nat} {program : Vector instruction p}
    {memories : Nat → PartialMemory m} (fragment : SetXorFragment program memories) :
    ArithmeticFragment program memories := fun i hi => .setXor (fragment i hi)

/-- Memory-policy admissibility derives every MUL, XOR, and SET step, including
MUL steps preceded by compatible candidate advice. The sentinel is unexecuted. -/
theorem arithmetic_trace {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (positive : 1 ≤ p) (programDomain : GPowerDomain p) (memoryDomain : GPowerDomain m)
    (memories : Nat → PartialMemory m) (fragment : ArithmeticFragment program memories)
    (finished : Completes (memories (p - 1)) (vectorImage mem)) :
    StepTrace program mem registersAt (p - 1) := by
  have growth : ∀ i, i < p - 1 → Evolves (memories i) (memories (i + 1)) :=
    fun i hi => (fragment i hi).evolves
  apply straightline_trace program mem positive programDomain
  intro i hi
  exact (fragment i hi).simulates mem memoryDomain
    (evolves_suffix memories (p - 1) growth (i + 1) (by omega)) finished

/-- Exact registers and halt/fuel behavior for the SET/XOR/MUL fragment of the
extracted Sail runner. Advice is checked, and effective-address equations remain explicit. -/
theorem run_arithmetic {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (fuel : Nat) (valid : ValidInstance program mem publicInput)
    (programDomain : GPowerDomain p) (memoryDomain : GPowerDomain m)
    (memories : Nat → PartialMemory m) (fragment : ArithmeticFragment program memories)
    (finished : Completes (memories (p - 1)) (vectorImage mem)) :
    run program mem publicInput fuel =
      ⟨registersAt (min fuel (p - 1)), if p - 1 ≤ fuel then .Halted else .OutOfFuel⟩ := by
  exact run_straightline program mem publicInput fuel valid
    (arithmetic_trace program mem valid.programPositive programDomain memoryDomain
      memories fragment finished)

end Leanisa.Proofs

#print axioms Leanisa.Proofs.mul_policy_simulates_step
#print axioms Leanisa.Proofs.mul_advice_simulates_step
#print axioms Leanisa.Proofs.mul_preserves_known_output
#print axioms Leanisa.Proofs.ArithmeticStep.simulates

#print axioms Leanisa.Proofs.arithmetic_trace
#print axioms Leanisa.Proofs.run_arithmetic
