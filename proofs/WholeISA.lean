import Arithmetic
import Dereference
import Compression

namespace Leanisa.Proofs
open Sail Leanisa.Functions

/-- The six instruction policies with complete next registers and explicit
per-step deferred equalities. No concrete Sail step result is a premise. -/
inductive IsaStep {m : Nat} (s : machine_state) :
    PartialMemory m → instruction → PartialMemory m → machine_state →
      List (Fin m × Fin m) → Prop where
  | arithmetic {before after ins} (operation : ArithmeticStep s before ins after) :
      IsaStep s before ins after (advancedState s) []
  | jump {before after ins next} (operation : JumpStep s before ins after next) :
      IsaStep s before ins after next []
  | deref {before after ins pending} (operation : DerefStep s before ins after pending) :
      IsaStep s before ins after (advancedState s) pending
  | blake {before after ins} (operation : BlakeStep s before ins after) :
      IsaStep s before ins after (advancedState s) []

theorem IsaStep.evolves {m : Nat} {s next : machine_state}
    {before after : PartialMemory m} {ins pending}
    (operation : IsaStep s before ins after next pending) : Evolves before after := by
  cases operation with
  | arithmetic operation => exact operation.evolves
  | jump operation => exact operation.evolves
  | deref operation => exact operation.evolves
  | blake operation => exact operation.evolves

theorem IsaStep.simulates {m : Nat} (mem : Vector Word m) (domain : GPowerDomain m)
    {s next : machine_state} {before after later : PartialMemory m} {ins pending}
    (operation : IsaStep s before ins after next pending) (continuation : Evolves after later)
    (finished : Completes later (vectorImage mem))
    (resolved : Resolves pending (vectorImage mem)) :
    step s ins mem = ⟨next, .Running⟩ := by
  cases operation with
  | arithmetic operation => exact operation.simulates mem domain continuation finished
  | jump operation => exact operation.simulates mem domain continuation finished
  | deref operation => exact operation.simulates mem domain continuation finished resolved
  | blake operation => exact operation.simulates mem domain continuation finished

/-- A finite policy execution. Program positions may repeat and frames may
change. Only executed positions are bounded and excluded from the sentinel;
the endpoint may halt, loop, or fail at its next fetch or instruction. -/
structure IsaPrefix {p m : Nat} (program : Vector instruction p)
    (states : Nat → machine_state) (memories : Nat → PartialMemory m)
    (pending : Nat → List (Fin m × Fin m)) (steps : Nat) : Prop where
  initial : states 0 = initialState
  progress : ∀ i, i < steps → ∃ position : Fin p,
    (states i).pc = gAddress position.val ∧ position.val ≠ p - 1 ∧
    IsaStep (states i) (memories i) (program.get position) (memories (i + 1))
      (states (i + 1)) (pending i)

theorem IsaPrefix.growth {p m : Nat} {program : Vector instruction p}
    {states : Nat → machine_state} {memories : Nat → PartialMemory m}
    {pending : Nat → List (Fin m × Fin m)} {steps : Nat}
    (chain : IsaPrefix program states memories pending steps) :
    ∀ i, i < steps → Evolves (memories i) (memories (i + 1)) := by
  intro i hi
  obtain ⟨position, maps, beforeSentinel, operation⟩ := chain.progress i hi
  exact operation.evolves

/-- Derive actual fetches and instruction results from the policy, lookup
bridge, suffix observation preservation, and resolution of every step's pending
equalities against the same completed image. No eventual halt is required. -/
theorem isa_step_prefix {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (positive : 1 ≤ p) (programDomain : GPowerDomain p) (memoryDomain : GPowerDomain m)
    (states : Nat → machine_state) (memories : Nat → PartialMemory m)
    (pending : Nat → List (Fin m × Fin m)) (steps : Nat)
    (chain : IsaPrefix program states memories pending steps)
    (finished : Completes (memories steps) (vectorImage mem))
    (resolved : ∀ i, i < steps → Resolves (pending i) (vectorImage mem)) :
    StepPrefix program mem states steps := by
  refine ⟨chain.initial, ?_⟩
  intro i hi
  obtain ⟨position, maps, beforeSentinel, operation⟩ := chain.progress i hi
  constructor
  · intro equal
    have addresses : gAddress position.val = gAddress (p - 1) := by
      rw [← maps, equal, sentinel_gAddress program positive]
    have indexEq := congrArg Fin.val
      (programDomain.distinct position ⟨p - 1, by omega⟩ addresses)
    exact beforeSentinel indexEq
  · refine ⟨program.get position, ?_, ?_⟩
    · rw [maps]
      exact fetch_gAddress program programDomain position
    · exact operation.simulates mem memoryDomain
        (evolves_suffix memories steps chain.growth (i + 1) (by omega)) finished (resolved i hi)

/-- A bounded nonterminal policy prefix returns exactly its fuel-prefix state.
In particular `fuel = steps` can describe a genuine loop with no halting extension. -/
theorem run_isa_out_of_fuel {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (fuel steps : Nat) (valid : ValidInstance program mem publicInput)
    (programDomain : GPowerDomain p) (memoryDomain : GPowerDomain m)
    (states : Nat → machine_state) (memories : Nat → PartialMemory m)
    (pending : Nat → List (Fin m × Fin m))
    (chain : IsaPrefix program states memories pending steps)
    (finished : Completes (memories steps) (vectorImage mem))
    (resolved : ∀ i, i < steps → Resolves (pending i) (vectorImage mem))
    (bounded : fuel ≤ steps) (nonterminal : (states fuel).pc ≠ sentinel program) :
    run program mem publicInput fuel = ⟨states fuel, .OutOfFuel⟩ := by
  exact run_prefix_out_of_fuel program mem publicInput fuel steps valid states
    (isa_step_prefix program mem valid.programPositive programDomain memoryDomain
      states memories pending steps chain finished resolved) bounded nonterminal

/-- Strictly smaller fuel needs no extra endpoint premise. -/
theorem run_isa_short {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (fuel steps : Nat) (valid : ValidInstance program mem publicInput)
    (programDomain : GPowerDomain p) (memoryDomain : GPowerDomain m)
    (states : Nat → machine_state) (memories : Nat → PartialMemory m)
    (pending : Nat → List (Fin m × Fin m))
    (chain : IsaPrefix program states memories pending steps)
    (finished : Completes (memories steps) (vectorImage mem))
    (resolved : ∀ i, i < steps → Resolves (pending i) (vectorImage mem)) (short : fuel < steps) :
    run program mem publicInput fuel = ⟨states fuel, .OutOfFuel⟩ := by
  exact run_prefix_short program mem publicInput fuel steps valid states
    (isa_step_prefix program mem valid.programPositive programDomain memoryDomain
      states memories pending steps chain finished resolved) short

/-- Complete fuel accounting for a policy chain ending at the sentinel. The
sentinel is never executed, and a non-unit terminal frame yields BadValue. -/
theorem run_isa_terminal {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (fuel steps : Nat) (valid : ValidInstance program mem publicInput)
    (programDomain : GPowerDomain p) (memoryDomain : GPowerDomain m)
    (states : Nat → machine_state) (memories : Nat → PartialMemory m)
    (pending : Nat → List (Fin m × Fin m))
    (chain : IsaPrefix program states memories pending steps)
    (finished : Completes (memories steps) (vectorImage mem))
    (resolved : ∀ i, i < steps → Resolves (pending i) (vectorImage mem))
    (terminal : (states steps).pc = sentinel program) :
    run program mem publicInput fuel =
      ⟨states (min fuel steps), if steps ≤ fuel then
        (if (states steps).fp == 1 then .Halted else .BadValue) else .OutOfFuel⟩ := by
  have concrete := isa_step_prefix program mem valid.programPositive programDomain memoryDomain
    states memories pending steps chain finished resolved
  by_cases enough : steps ≤ fuel
  · simpa only [enough, ↓reduceIte, Nat.min_eq_right enough] using
      run_prefix_terminal program mem publicInput fuel steps valid states concrete terminal enough
  · have short : fuel < steps := by omega
    simpa only [enough, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt short)] using
      run_prefix_short program mem publicInput fuel steps valid states concrete short

end Leanisa.Proofs

#print axioms Leanisa.Proofs.IsaStep.simulates
#print axioms Leanisa.Proofs.isa_step_prefix
#print axioms Leanisa.Proofs.run_isa_out_of_fuel
#print axioms Leanisa.Proofs.run_isa_short
#print axioms Leanisa.Proofs.run_isa_terminal
