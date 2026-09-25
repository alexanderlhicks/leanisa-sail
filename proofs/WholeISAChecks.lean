import WholeISA

/-! Kernel-checked interface regressions for the zero-step and genuinely looping
cases. These instantiate policy runner theorems without an eventual-halt premise. -/
namespace Leanisa.Proofs.WholeISAChecks
open Sail Leanisa.Functions

/-- A stable policy self-loop has a successful finite prefix for every budget.
There is no assumption that this execution can ever reach the sentinel. -/
theorem stable_loop_all_budgets {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256)
    (valid : ValidInstance program mem publicInput)
    (programDomain : GPowerDomain p) (memoryDomain : GPowerDomain m)
    (memory : PartialMemory m) (pending : List (Fin m × Fin m)) (position : Fin p)
    (maps : initialState.pc = gAddress position.val) (beforeSentinel : position.val ≠ p - 1)
    (operation : IsaStep initialState memory (program.get position) memory initialState pending)
    (finished : Completes memory (vectorImage mem)) (resolved : Resolves pending (vectorImage mem))
    (fuel : Nat) : run program mem publicInput fuel = ⟨initialState, .OutOfFuel⟩ := by
  have chain : IsaPrefix program (fun _ => initialState) (fun _ => memory) (fun _ => pending) fuel :=
    ⟨rfl, fun _ _ => ⟨position, maps, beforeSentinel, operation⟩⟩
  have nonterminal : initialState.pc ≠ sentinel program := by
    intro equal
    have addresses : gAddress position.val = gAddress (p - 1) := by
      rw [← maps, equal, sentinel_gAddress program valid.programPositive]
    have hp := valid.programPositive
    exact beforeSentinel (congrArg Fin.val
      (programDomain.distinct position ⟨p - 1, by omega⟩ addresses))
  exact run_isa_out_of_fuel program mem publicInput fuel fuel valid programDomain memoryDomain
    (fun _ => initialState) (fun _ => memory) (fun _ => pending) chain finished
    (fun _ _ => resolved) (Nat.le_refl _) nonterminal

/-- A valid singleton never executes its sole instruction, for any fuel. -/
theorem singleton_all_budgets {m : Nat} (program : Vector instruction 1)
    (mem : Vector Word m) (publicInput : BitVec 256)
    (valid : ValidInstance program mem publicInput)
    (programDomain : GPowerDomain 1) (memoryDomain : GPowerDomain m)
    (memory : PartialMemory m) (finished : Completes memory (vectorImage mem)) (fuel : Nat) :
    run program mem publicInput fuel = ⟨initialState, .Halted⟩ := by
  have chain : IsaPrefix program (fun _ => initialState) (fun _ => memory) (fun _ => []) 0 :=
    ⟨rfl, fun _ impossible => by omega⟩
  have terminal : initialState.pc = sentinel program := by
    simp [initialState, sentinel_gAddress program (by decide), programDomain.origin]
  simpa [initialState] using
    run_isa_terminal program mem publicInput fuel 0 valid programDomain memoryDomain
      (fun _ => initialState) (fun _ => memory) (fun _ => []) chain finished
      (fun _ impossible => by omega) terminal

end Leanisa.Proofs.WholeISAChecks

#print axioms Leanisa.Proofs.WholeISAChecks.stable_loop_all_budgets
#print axioms Leanisa.Proofs.WholeISAChecks.singleton_all_budgets
