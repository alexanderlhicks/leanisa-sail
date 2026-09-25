import EncodedBoundaries

noncomputable section
open Leanisa Leanisa.Proofs Leanisa.Proofs.Quotient Leanisa.Functions Sail
namespace Leanisa.Proofs.Encoded

theorem observed_known {m : Nat} (memory : PartialMemory m)
    (indices : List (Fin m)) (v : Word)
    (fixed : ∀ i ∈ indices, memory i = some v) :
    Observed memory (indices.map (fun i => (i, v))) memory := by
  induction indices with
  | nil => exact .nil _
  | cons a rest ih =>
    have first : observeZero memory a = (v, memory) := by
      simp [observeZero, fixed a (by simp)]
    have remaining : ∀ i ∈ rest, memory i = some v := by
      intro i hi
      exact fixed i (by simp [hi])
    have tail : Observed (observeZero memory a).2
        (rest.map (fun i => (i, v))) memory := by
      simpa only [first] using ih remaining
    simpa [List.map, first] using Observed.cons memory a tail

/-- Fully aliased XOR with zero-default observation is an admitted encoded step. -/
theorem all_alias_xor (a : Fin 1) :
    IsaStep initialState (fun _ : Fin 1 => none)
      (.Xor (gAddress 0, gAddress 0, gAddress 0))
      (fun b => if b = a then some 0 else none) (advancedState initialState) [] := by
  have index : a.val = 0 + 0 := by have := a.isLt; omega
  exact encoded_xor initialState 0 0 0 0 a a a (by decide)
    (by simp [initialState, gAddress_origin]) index index index (xor_empty_all_alias a)

/-- All-alias MUL remains available when its checked ordered operation succeeds. -/
theorem all_alias_mul {m : Nat} (s : machine_state) (a : Fin m)
    {before after : PartialMemory m} (bound : m ≤ 2^32)
    (frameRep : s.fp = gAddress a.val)
    (assigned : mulAssign before a a a = some after) :
    IsaStep s before (.Mul (gAddress 0, gAddress 0, gAddress 0))
      after (advancedState s) [] :=
  encoded_mul s a.val 0 0 0 a a a bound frameRep
    (by omega) (by omega) (by omega) assigned

/-- A fixed zero cell is a concrete compatible all-alias MUL product. -/
theorem zero_all_alias_mul (a : Fin 1) :
    IsaStep initialState (fun _ : Fin 1 => some (0 : Word))
      (.Mul (gAddress 0, gAddress 0, gAddress 0))
      (fun _ => some (0 : Word)) (advancedState initialState) [] := by
  have product : emul (0#192) (0#192) = 0#192 := by decide +kernel
  have assigned : mulAssign (fun _ : Fin 1 => some (0 : Word)) a a a =
      some (fun _ => some (0 : Word)) := by
    rw [mul_all_alias_known (fun _ : Fin 1 => some (0 : Word)) a 0 (by rfl)]
    simp [product]
  have index : a.val = 0 + 0 := by have := a.isLt; omega
  exact encoded_mul initialState 0 0 0 0 a a a (by decide)
    (by simp [initialState, gAddress_origin]) index index index assigned

/-- The checked-advice variant accepts the same zero alias only with consistent advice. -/
theorem zero_all_alias_mul_advice (a : Fin 1) :
    IsaStep initialState (fun _ : Fin 1 => some (0 : Word))
      (.Mul (gAddress 0, gAddress 0, gAddress 0))
      (fun _ => some (0 : Word)) (advancedState initialState) [] := by
  have product : emul (0#192) (0#192) = 0#192 := by decide +kernel
  have assigned : mulAssignWithAdvice (fun _ : Fin 1 => some (0 : Word)) a 0 a a a =
      some (fun _ => some (0 : Word)) := by
    simp [mulAssignWithAdvice, assign, mulAssign, observeZero, product]
  have index : a.val = 0 + 0 := by have := a.isLt; omega
  exact encoded_mul_advice initialState 0 0 0 0 a a a a 0 (by decide)
    (by simp [initialState, gAddress_origin]) index index index assigned

/-- Fallthrough accepts loaded K words whose low words have no supported address. -/
theorem zero_loaded_fallthrough (a : Fin 1) :
    IsaStep initialState (fun _ : Fin 1 => some (0 : Word))
      (.Jump (gAddress 0, gAddress 0, gAddress 0))
      (fun _ => some (0 : Word)) (advancedState initialState) [] := by
  have index : a.val = 0 + 0 := by have := a.isLt; omega
  have reads : Observed (fun _ : Fin 1 => some (0 : Word))
      [(a, 0), (a, 0), (a, 0)] (fun _ => some (0 : Word)) := by
    simpa using observed_known (fun _ : Fin 1 => some (0 : Word)) [a, a, a] 0
      (by intro i hi; rfl)
  exact encoded_jump_fallthrough initialState 0 0 0 0 a a a 0 0 0
    (by decide) (by simp [initialState, gAddress_origin]) index index index
    reads (by decide) (by decide) (by decide) (by decide)

/-- The represented taken branch is derived from the loaded low-word equations. -/
theorem one_loaded_taken (a : Fin 1) :
    IsaStep initialState (fun _ : Fin 1 => some (1 : Word))
      (.Jump (gAddress 0, gAddress 0, gAddress 0))
      (fun _ => some (1 : Word)) ⟨gAddress 0, gAddress 0⟩ [] := by
  have index : a.val = 0 + 0 := by have := a.isLt; omega
  have reads : Observed (fun _ : Fin 1 => some (1 : Word))
      [(a, 1), (a, 1), (a, 1)] (fun _ => some (1 : Word)) := by
    simpa using observed_known (fun _ : Fin 1 => some (1 : Word)) [a, a, a] 1
      (by intro i hi; rfl)
  exact encoded_jump_taken initialState 0 0 0 0 a a a 1 1 1 0 0
    (by decide) (by simp [initialState, gAddress_origin]) index index index
    reads (by decide) (by decide) (by decide) (by decide)
    (by rw [gAddress_origin]; decide) (by rw [gAddress_origin]; decide)

/-- Pointer, syntactic source, and target may be the same cell in Cell mode. -/
theorem cell_all_alias (a : Fin 1) :
    IsaStep initialState (fun _ : Fin 1 => some (1 : Word))
      (.Deref (gAddress 0, gAddress 0, gAddress 0, .Cell))
      (fun _ => some (1 : Word)) (advancedState initialState) [(a, a)] := by
  have index : a.val = 0 + 0 := by have := a.isLt; omega
  have reads : Observed (fun _ : Fin 1 => some (1 : Word))
      [(a, 1)] (fun _ => some (1 : Word)) := by
    simpa using observed_known (fun _ : Fin 1 => some (1 : Word)) [a] 1
      (by intro i hi; rfl)
  exact encoded_deref_cell initialState 0 0 0 0 0 a a a 1
    (by decide) (by simp [initialState, gAddress_origin]) index index index
    (by rw [gAddress_origin]; decide) reads (by decide)

/-- An eager observation cannot be overwritten with a contradictory value. -/
theorem observed_write_conflict {m : Nat} {before observed : PartialMemory m}
    (a : Fin m) (old new : Word)
    (reads : Observed before [(a, old)] observed) (different : new ≠ old) :
    assign observed a new = none := by
  have fixed : observed a = some old := reads.fixed a old (by simp)
  simp [assign, fixed, Ne.symm different]

/-- A one-step encoded SET policy composes with the extracted step theorem. -/
theorem set_supported_step {m : Nat} (mem : Vector Word m) (s : machine_state)
    (frame offset : Nat) (target : Fin m) (value : Word)
    {before after later : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (index : target.val = frame + offset)
    (assigned : assign before target value = some after)
    (continuation : Evolves after later)
    (finished : Completes later (vectorImage mem)) :
    step s (.Set (gAddress offset, value)) mem = ⟨advancedState s, .Running⟩ := by
  exact Supported.supported_step mem bound
    (encoded_set s frame offset target value bound frameRep index assigned)
    continuation finished (by intro pair h; simp at h)

/-- A finite policy prefix built from an encoded SET derives a concrete StepPrefix. -/
theorem one_set_prefix {m : Nat} (program : Vector instruction 2) (mem : Vector Word m)
    (publicInput : BitVec 256) (valid : ValidInstance program mem publicInput)
    (value : Word) (target : Fin m) {before after : PartialMemory m}
    (programAt : program.get ⟨0, by decide⟩ = .Set (gAddress target.val, value))
    (assigned : assign before target value = some after)
    (finished : Completes after (vectorImage mem)) :
    StepPrefix program mem
      (fun i => if i = 0 then initialState else advancedState initialState) 1 := by
  let states : Nat → machine_state := fun i => if i = 0 then initialState else advancedState initialState
  let memories : Nat → PartialMemory m := fun i => if i = 0 then before else after
  let pending : Nat → List (Fin m × Fin m) := fun _ => []
  have chain : IsaPrefix program states memories pending 1 := by
    constructor
    · rfl
    · intro i hi
      have iz : i = 0 := by omega
      subst i
      refine ⟨⟨0, by decide⟩, ?_, ?_, ?_⟩
      · simp [states, initialState, gAddress_origin]
      · decide
      · simp only [states, memories, pending, Nat.add_one_ne_zero, ↓reduceIte]
        rw [programAt]
        exact encoded_set initialState 0 target.val target value
          valid.memoryUpper (by simp [initialState, gAddress_origin])
          (by omega) assigned
  have completed : Completes (memories 1) (vectorImage mem) := by simpa [memories] using finished
  exact Supported.supported_prefix program mem publicInput valid states memories pending 1
    chain completed (by intro i hi pair h; simp [pending] at h)

end Leanisa.Proofs.Encoded
