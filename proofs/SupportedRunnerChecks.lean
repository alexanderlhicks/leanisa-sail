/-
Directed checks of supported runner-policy premises and finite-memory
boundaries. These checks exercise the included whole-ISA policy theorems.
-/
import SupportedAddressChecks

noncomputable section
open Leanisa Leanisa.Proofs Leanisa.Proofs.Quotient Leanisa.Functions
namespace Leanisa.Proofs.Supported

def emptyMemory (m : Nat) : PartialMemory m := fun _ => none

theorem initial_prefix {p m : Nat} (program : Vector instruction p) :
    IsaPrefix program (fun _ => initialState) (fun _ => emptyMemory m) (fun _ => []) 0 := by
  constructor
  · rfl
  · intro i hi
    omega

theorem initial_complete {m : Nat} (mem : Vector Word m) :
    Completes (emptyMemory m) (vectorImage mem) := by
  intro a v assigned
  cases assigned

/-- Aliasing remains admitted by the existing policy. The effective-address
mapping is explicitly retained; encoded-offset constructors require separate premises. -/
theorem all_alias_xor_policy {m : Nat} (s : machine_state) (operand : BitVec 64)
    (target : Fin m) {before after : PartialMemory m}
    (maps : kmul s.fp operand = gAddress target.val)
    (assigned : xorAssign before target target target = some after) :
    SetXorStep s before (.Xor (operand, operand, operand)) after :=
  .xor _ _ _ target target target maps maps maps assigned

theorem singleton_zero_step_halt {m : Nat} (program : Vector instruction 1)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel : Nat)
    (valid : ValidInstance program mem publicInput) :
    run program mem publicInput fuel = ⟨initialState, .Halted⟩ := by
  have terminal : initialState.pc = sentinel program := by
    rw [sentinel_gAddress program (by decide), show 1 - 1 = 0 by decide, gAddress_origin]
    rfl
  have result := supported_terminal program mem publicInput fuel 0 valid
    (fun _ => initialState) (fun _ => emptyMemory m) (fun _ => [])
    (initial_prefix program) (initial_complete mem) (by intro i hi; omega) terminal
  simpa [initialState] using result

theorem nonsingleton_zero_fuel {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256)
    (valid : ValidInstance program mem publicInput) (longer : 2 ≤ p) :
    run program mem publicInput 0 = ⟨initialState, .OutOfFuel⟩ := by
  have nonterminal : initialState.pc ≠ sentinel program := by
    intro equal
    have addresses : gAddress 0 = gAddress (p - 1) := by
      rw [gAddress_origin, ← sentinel_gAddress program valid.programPositive]
      exact equal
    have positions := (supported_domain p valid.programUpper).distinct
      ⟨0, by omega⟩ ⟨p - 1, by omega⟩ addresses
    have values := congrArg Fin.val positions
    change 0 = p - 1 at values
    omega
  exact supported_out_of_fuel program mem publicInput 0 0 valid
    (fun _ => initialState) (fun _ => emptyMemory m) (fun _ => [])
    (initial_prefix program) (initial_complete mem) (by intro i hi; omega)
    (by decide) nonterminal

/-- A nonempty policy prefix gives the strict-short zero-fuel result without
assuming a halting extension or adding an endpoint nonsentinel premise. -/
theorem zero_fuel_before_nonempty_prefix {p m : Nat}
    (program : Vector instruction p) (mem : Vector Word m) (publicInput : BitVec 256)
    (valid : ValidInstance program mem publicInput)
    (states : Nat → machine_state) (memories : Nat → PartialMemory m)
    (pending : Nat → List (Fin m × Fin m)) (steps : Nat)
    (chain : IsaPrefix program states memories pending steps)
    (finished : Completes (memories steps) (vectorImage mem))
    (resolved : ∀ i, i < steps → Resolves (pending i) (vectorImage mem))
    (nonempty : 0 < steps) :
    run program mem publicInput 0 = ⟨initialState, .OutOfFuel⟩ := by
  have result := supported_short program mem publicInput 0 steps valid
    states memories pending chain finished resolved nonempty
  rw [chain.initial] at result
  exact result

end Leanisa.Proofs.Supported
