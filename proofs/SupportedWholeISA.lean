/-
Connects supported finite address domains to the conditional whole-ISA
instruction policies. Concrete operand mappings and all observation,
completion, and resolution premises remain explicit.
-/
import SupportedAddressDomain
import WholeISA

noncomputable section
open Leanisa Leanisa.Proofs Leanisa.Functions
namespace Leanisa.Proofs.Supported

theorem supported_step {m : Nat} (mem : Vector Word m) (bound : m ≤ 2^32)
    {s next : machine_state} {before after later : PartialMemory m} {ins pending}
    (operation : IsaStep s before ins after next pending) (continuation : Evolves after later)
    (finished : Completes later (vectorImage mem))
    (resolved : Resolves pending (vectorImage mem)) :
    step s ins mem = ⟨next, .Running⟩ :=
  operation.simulates mem (supported_domain m bound) continuation finished resolved

theorem supported_prefix {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (valid : ValidInstance program mem publicInput)
    (states : Nat → machine_state) (memories : Nat → PartialMemory m)
    (pending : Nat → List (Fin m × Fin m)) (steps : Nat)
    (chain : IsaPrefix program states memories pending steps)
    (finished : Completes (memories steps) (vectorImage mem))
    (resolved : ∀ i, i < steps → Resolves (pending i) (vectorImage mem)) :
    StepPrefix program mem states steps :=
  isa_step_prefix program mem valid.programPositive
    (supported_domain p valid.programUpper) (supported_domain m valid.memoryUpper)
    states memories pending steps chain finished resolved

/-- Strictly shorter fuel obtains a nonterminal executed position directly
from the policy prefix; no eventual halt or endpoint premise is added. -/
theorem supported_short {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (fuel steps : Nat) (valid : ValidInstance program mem publicInput)
    (states : Nat → machine_state) (memories : Nat → PartialMemory m)
    (pending : Nat → List (Fin m × Fin m))
    (chain : IsaPrefix program states memories pending steps)
    (finished : Completes (memories steps) (vectorImage mem))
    (resolved : ∀ i, i < steps → Resolves (pending i) (vectorImage mem))
    (short : fuel < steps) :
    run program mem publicInput fuel = ⟨states fuel, .OutOfFuel⟩ :=
  run_isa_short program mem publicInput fuel steps valid
    (supported_domain p valid.programUpper) (supported_domain m valid.memoryUpper)
    states memories pending chain finished resolved short

theorem supported_out_of_fuel {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (fuel steps : Nat) (valid : ValidInstance program mem publicInput)
    (states : Nat → machine_state) (memories : Nat → PartialMemory m)
    (pending : Nat → List (Fin m × Fin m))
    (chain : IsaPrefix program states memories pending steps)
    (finished : Completes (memories steps) (vectorImage mem))
    (resolved : ∀ i, i < steps → Resolves (pending i) (vectorImage mem))
    (bounded : fuel ≤ steps) (nonterminal : (states fuel).pc ≠ sentinel program) :
    run program mem publicInput fuel = ⟨states fuel, .OutOfFuel⟩ :=
  run_isa_out_of_fuel program mem publicInput fuel steps valid
    (supported_domain p valid.programUpper) (supported_domain m valid.memoryUpper)
    states memories pending chain finished resolved bounded nonterminal

theorem supported_terminal {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (fuel steps : Nat) (valid : ValidInstance program mem publicInput)
    (states : Nat → machine_state) (memories : Nat → PartialMemory m)
    (pending : Nat → List (Fin m × Fin m))
    (chain : IsaPrefix program states memories pending steps)
    (finished : Completes (memories steps) (vectorImage mem))
    (resolved : ∀ i, i < steps → Resolves (pending i) (vectorImage mem))
    (terminal : (states steps).pc = sentinel program) :
    run program mem publicInput fuel =
      ⟨states (min fuel steps), if steps ≤ fuel then
        (if (states steps).fp == 1 then .Halted else .BadValue) else .OutOfFuel⟩ :=
  run_isa_terminal program mem publicInput fuel steps valid
    (supported_domain p valid.programUpper) (supported_domain m valid.memoryUpper)
    states memories pending chain finished resolved terminal

end Leanisa.Proofs.Supported
