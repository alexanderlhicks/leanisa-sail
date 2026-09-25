import Lookup

namespace Leanisa.Proofs
open Sail Leanisa.Functions

/-- The actual next state of a successful non-branching Sail instruction. -/
def advancedState (s : machine_state) : machine_state := ⟨advance s.pc, s.fp⟩

@[simp] theorem read_memory_indexed_empty {n : Nat} (mem : Vector Word n)
    (index : Vector address_entry 0) (address : BitVec 64) :
    read_memory_indexed mem index address = read_memory mem address := by
  rfl

theorem step_set_of_read {n : Nat} (mem : Vector Word n) (s : machine_state)
    (offset : BitVec 64) (v : Word)
    (read : read_memory mem (kmul s.fp offset) = ⟨v, true⟩) :
    step s (.Set (offset, v)) mem = ⟨advancedState s, .Running⟩ := by
  simp only [step, step_indexed, read_memory_indexed_empty, read]
  simp [advancedState, show (status.Running == status.Running) = true from rfl]

theorem step_xor_of_reads {n : Nat} (mem : Vector Word n) (s : machine_state)
    (oa ob oc : BitVec 64) (va vb : Word)
    (ra : read_memory mem (kmul s.fp oa) = ⟨va, true⟩)
    (rb : read_memory mem (kmul s.fp ob) = ⟨vb, true⟩)
    (rc : read_memory mem (kmul s.fp oc) = ⟨va ^^^ vb, true⟩) :
    step s (.Xor (oa, ob, oc)) mem = ⟨advancedState s, .Running⟩ := by
  simp only [step, step_indexed, read_memory_indexed_empty, ra, rb, rc]
  simp [advancedState, show (status.Running == status.Running) = true from rfl]

/-- A compatible SET assignment, followed by compatible evolution and completion,
simulates the actual extracted Sail step. Effective-address arithmetic is a hypothesis. -/
theorem assignment_simulates_set {n : Nat} (mem : Vector Word n) (domain : GPowerDomain n)
    (s : machine_state) (offset : BitVec 64) (i : Fin n) (v : Word)
    {memory next later : PartialMemory n}
    (maps : kmul s.fp offset = gAddress i.val)
    (assigned : assign memory i v = some next)
    (execution : Evolves next later)
    (finished : Completes later (vectorImage mem)) :
    step s (.Set (offset, v)) mem = ⟨advancedState s, .Running⟩ := by
  apply step_set_of_read
  exact completed_cell_lookup mem domain finished i v
    (execution_extends execution i v (assign_fixes_value assigned)) _ maps

/-- Observe both operands sequentially, then assign their XOR consistently.
There are no disjointness conditions: either input may alias the other or the output. -/
def xorAssign {n : Nat} (memory : PartialMemory n) (a b c : Fin n) :
    Option (PartialMemory n) :=
  let first := observeZero memory a
  let second := observeZero first.2 b
  assign second.2 c (first.1 ^^^ second.1)

/-- Compatible completion of the observation policy establishes an XOR step,
including all input/output aliasing patterns. No theorem about Rust reads is assumed. -/
theorem xor_policy_simulates_step {n : Nat} (mem : Vector Word n) (domain : GPowerDomain n)
    (s : machine_state) (oa ob oc : BitVec 64) (a b c : Fin n)
    {memory next later : PartialMemory n}
    (maps_a : kmul s.fp oa = gAddress a.val)
    (maps_b : kmul s.fp ob = gAddress b.val)
    (maps_c : kmul s.fp oc = gAddress c.val)
    (assigned : xorAssign memory a b c = some next)
    (execution : Evolves next later)
    (finished : Completes later (vectorImage mem)) :
    step s (.Xor (oa, ob, oc)) mem = ⟨advancedState s, .Running⟩ := by
  let first := observeZero memory a
  let second := observeZero first.2 b
  have write : assign second.2 c (first.1 ^^^ second.1) = some next := assigned
  have second_later : Extends second.2 later :=
    extends_trans (assign_extends write) (execution_extends execution)
  have first_later : Extends first.2 later :=
    extends_trans (observe_extends first.2 b) second_later
  apply step_xor_of_reads mem s oa ob oc first.1 second.1
  · exact completed_cell_lookup mem domain finished a first.1
      (first_later a first.1 (observe_fixes_value memory a)) _ maps_a
  · exact completed_cell_lookup mem domain finished b second.1
      (second_later b second.1 (observe_fixes_value first.2 b)) _ maps_b
  · exact completed_cell_lookup mem domain finished c (first.1 ^^^ second.1)
      (execution_extends execution c _ (assign_fixes_value write)) _ maps_c

/-- Fully aliased zero inputs are admissible, even before any explicit write. -/
theorem xor_empty_all_alias {n : Nat} (a : Fin n) :
    xorAssign (fun _ => none) a a a =
      some (fun b => if b = a then some 0 else none) := by
  simp [xorAssign, observeZero, assign]

/-- The same fully aliased instruction cannot overwrite an observed nonzero word. -/
theorem xor_all_alias_rejects_nonzero {n : Nat} (memory : PartialMemory n) (a : Fin n)
    (nonzero : (observeZero memory a).1 ≠ 0) :
    xorAssign memory a a a = none := by
  cases fixed : memory a with
  | none => simp [observeZero, fixed] at nonzero
  | some v =>
    simp only [observeZero, fixed] at nonzero
    simp [xorAssign, observeZero, fixed, assign]
    exact nonzero

/-- An output alias cannot change an input observed as zero within the same instruction.
This is the eager-observation analogue of the existing Rust alias counterexample. -/
theorem xor_output_alias_rejects_change {n : Nat} (memory : PartialMemory n)
    (a b : Fin n) (v : Word) (empty : memory a = none) (fixed : memory b = some v)
    (nonzero : v ≠ 0) : xorAssign memory a b a = none := by
  have distinct : b ≠ a := by
    intro eq
    subst b
    rw [empty] at fixed
    contradiction
  simp [xorAssign, observeZero, empty, distinct, fixed, assign]
  exact Ne.symm nonzero

end Leanisa.Proofs

#print axioms Leanisa.Proofs.assignment_simulates_set
#print axioms Leanisa.Proofs.xor_policy_simulates_step
#print axioms Leanisa.Proofs.xor_empty_all_alias
#print axioms Leanisa.Proofs.xor_all_alias_rejects_nonzero
#print axioms Leanisa.Proofs.xor_output_alias_rejects_change
