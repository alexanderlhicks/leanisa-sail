import IndexedRunner
import IndexedChecks

namespace Leanisa.Proofs.I1c2.Checks
open Sail Leanisa Leanisa.Functions Leanisa.Proofs

private def s : machine_state := ⟨1, 1⟩
private def emptyMem : Vector Word 0 := #v[]
private def oneMem : Vector Word 1 := #v[7]
def oneProgram : Vector instruction 1 := #v[.Set (1, 7)]
def twoProgram : Vector instruction 2 := #v[.Set (1, 7), .Set (2, 9)]

private theorem addr_one : kmul s.fp 1 = 1#64 := by decide +kernel
private theorem addr_two : kmul s.fp 2 = 2#64 := by decide +kernel
private theorem hit_valid :
    (read_memory_indexed oneMem (build_address_index 1) (1#64)).valid = true := by
  decide +kernel
private theorem hit_value :
    (read_memory_indexed oneMem (build_address_index 1) (1#64)).value = 7#192 := by
  decide +kernel
private theorem miss_valid :
    (read_memory_indexed oneMem (build_address_index 1) (2#64)).valid = false := by
  decide +kernel

/-- A missing address has priority over a false value relation. -/
theorem missing_read_is_bad_access :
    step_indexed s (.Set (2, 9)) oneMem (build_address_index 1) =
      ⟨s, .BadAccess⟩ := by
  simp only [step_indexed, addr_two]
  rw [miss_valid]
  have hstatus : (status.BadAccess == status.Running) = false := by decide +kernel
  simp [hstatus]

/-- A present address with a wrong word is a value error. -/
theorem wrong_value_is_bad_value :
    step_indexed s (.Set (1, 9)) oneMem (build_address_index 1) =
      ⟨s, .BadValue⟩ := by
  simp only [step_indexed, addr_one]
  rw [hit_valid, hit_value]
  have hstatus : (status.BadValue == status.Running) = false := by decide +kernel
  simp [hstatus]

/-- A failed branch returns the original state, despite computing a tentative next state. -/
theorem failed_jump_keeps_original_state :
    step_indexed s (.Jump (1, 2, 1)) oneMem (build_address_index 1) =
      ⟨s, .BadAccess⟩ := by
  simp only [step_indexed, addr_one, addr_two]
  rw [hit_valid, miss_valid]
  have hstatus : (status.BadAccess == status.Running) = false := by decide +kernel
  simp [hstatus]

private theorem forged_step_bad_value :
    step_indexed s (.Set (1, 7)) I1c1.Checks.twoMemory
      I1c1.Checks.wrongOffsetTable = ⟨s, .BadValue⟩ := by
  simp only [step_indexed, addr_one]
  have facts := I1c1.Checks.forged_wrong_offset_values
  have hv : (read_memory_indexed I1c1.Checks.twoMemory
      I1c1.Checks.wrongOffsetTable (1#64)).valid = true := by
    simpa using facts.1
  have hval : (read_memory_indexed I1c1.Checks.twoMemory
      I1c1.Checks.wrongOffsetTable (1#64)).value = 9#192 := by
    simpa using facts.2.2.1
  rw [hv, hval]
  have hstatus : (status.BadValue == status.Running) = false := by decide +kernel
  simp [hstatus]

private theorem scanned_step_running :
    step s (.Set (1, 7)) I1c1.Checks.twoMemory =
      ⟨advancedState s, .Running⟩ := by
  apply step_set_of_read
  have domain : GPowerDomain 2 := Supported.supported_domain 2 (by omega)
  have hit := read_memory_gAddress I1c1.Checks.twoMemory domain
    (⟨0, by omega⟩ : Fin 2)
  have haddr : gAddress 0 = kmul s.fp 1 := by decide +kernel
  rw [haddr] at hit
  simpa [I1c1.Checks.twoMemory] using hit

/-- Equal validity flags alone do not imply equal step results. The forged
    table reads the wrong value at an otherwise valid address. -/
theorem validity_only_does_not_imply_step :
    ¬ (∀ index : Vector address_entry 2,
      (read_memory_indexed I1c1.Checks.twoMemory index (1#64)).valid =
        (read_memory I1c1.Checks.twoMemory (1#64)).valid →
      step_indexed s (.Set (1, 7)) I1c1.Checks.twoMemory index =
        step s (.Set (1, 7)) I1c1.Checks.twoMemory) := by
  intro falseClaim
  have hv : (read_memory_indexed I1c1.Checks.twoMemory
      I1c1.Checks.wrongOffsetTable (1#64)).valid =
      (read_memory I1c1.Checks.twoMemory (1#64)).valid := by
    have h1 : (read_memory_indexed I1c1.Checks.twoMemory
      I1c1.Checks.wrongOffsetTable (1#64)).valid = true := by decide +kernel
    have h2 : (read_memory I1c1.Checks.twoMemory (1#64)).valid = true := by
      decide +kernel
    rw [h1, h2]
  have heq := falseClaim I1c1.Checks.wrongOffsetTable hv
  have hstatus := congrArg step_result.verdict heq
  rw [forged_step_bad_value, scanned_step_running] at hstatus
  cases hstatus

/-- The genuine builder relates all six instruction constructors, including
    DEREF's pointer-dependent address and the BLAKE reads. -/
theorem every_instruction_matches {m : Nat} (mem : Vector Word m)
    (bound : m ≤ 2^32) (state : machine_state) (ins : instruction) :
    step_indexed state ins mem (build_address_index m) = step state ins mem := by
  exact step_indexed_build_eq_step mem (Nat.le_refl m) bound state ins

/-- An invalid instance is rejected before the zero-fuel shortcut. -/
theorem invalid_precedes_zero_fuel :
    run_indexed oneProgram emptyMem 0 0 = ⟨initialState, .BadInstance⟩ ∧
    run oneProgram emptyMem 0 0 = ⟨initialState, .BadInstance⟩ := by
  have bad : indexedInvalid oneProgram emptyMem 0 = true := by decide +kernel
  simp only [run_indexed, run, ← indexedInvalid_model oneProgram emptyMem 0,
    bad, ↓reduceIte]
  exact ⟨rfl, rfl⟩

private theorem singleton_at_sentinel : initialState.pc = sentinel oneProgram := by
  decide +kernel
private theorem pair_not_at_sentinel : initialState.pc ≠ sentinel twoProgram := by
  decide +kernel

/-- In the good-instance branch, the singleton program halts at its initial
    sentinel even when the fuel is zero. -/
theorem singleton_initial_sentinel {m : Nat} (mem : Vector Word m)
    (input : BitVec 256) (fuel : Nat) (hm : 2 ≤ m)
    (good : indexedInvalid oneProgram mem input = false) :
    run_indexed oneProgram mem input fuel = ⟨initialState, .Halted⟩ ∧
    run oneProgram mem input fuel = ⟨initialState, .Halted⟩ := by
  have indexed := indexed_initial_sentinel oneProgram mem input fuel good
    singleton_at_sentinel
  have equal := run_indexed_eq_run oneProgram mem input fuel (by omega) hm
  exact ⟨indexed, equal.symm.trans indexed⟩

/-- In the good-instance branch, zero fuel stops before an attempted fetch. -/
theorem pair_zero_fuel {m : Nat} (mem : Vector Word m)
    (input : BitVec 256) (hm : 2 ≤ m)
    (good : indexedInvalid twoProgram mem input = false) :
    run_indexed twoProgram mem input 0 = ⟨initialState, .OutOfFuel⟩ ∧
    run twoProgram mem input 0 = ⟨initialState, .OutOfFuel⟩ := by
  have indexed := indexed_zero_fuel twoProgram mem input good pair_not_at_sentinel
  have equal := run_indexed_eq_run twoProgram mem input 0 (by omega) hm
  exact ⟨indexed, equal.symm.trans indexed⟩

/-- At the inclusive fuel boundary, a successful prefix reports exact exhaustion. -/
theorem indexed_trace_out_of_fuel {p m : Nat}
    (program : Vector instruction p) (mem : Vector Word m)
    (input : BitVec 256) (fuel steps : Nat)
    (hp : 1 ≤ p) (hm : 2 ≤ m)
    (valid : ValidInstance program mem input) (states : Nat → machine_state)
    (trace : StepTrace program mem states steps) (short : fuel < steps) :
    run_indexed program mem input fuel = ⟨states fuel, .OutOfFuel⟩ := by
  rw [run_indexed_eq_run program mem input fuel hp hm]
  exact run_trace_out_of_fuel program mem input fuel steps valid states trace short

/-- A later sentinel with a non-unit frame is a value error, not a halt. -/
theorem indexed_nonunit_sentinel_bad_value {p m : Nat}
    (program : Vector instruction p) (mem : Vector Word m)
    (input : BitVec 256) (fuel steps : Nat)
    (hp : 1 ≤ p) (hm : 2 ≤ m)
    (valid : ValidInstance program mem input) (states : Nat → machine_state)
    (trace : StepTrace program mem states steps) (enough : steps ≤ fuel)
    (nonunit : (states steps).fp ≠ 1) :
    run_indexed program mem input fuel = ⟨states steps, .BadValue⟩ := by
  rw [run_indexed_eq_run program mem input fuel hp hm]
  have ref := run_trace_terminal program mem input fuel steps valid states trace enough
  have hbool : ((states steps).fp == 1) = false := by simpa using nonunit
  rw [hbool] at ref
  simpa using ref

/-- The public result preserves both verdict and whole state at every fuel. -/
theorem all_fuel_and_states {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (input : BitVec 256)
    (hp : 1 ≤ p) (hm : 2 ≤ m) (fuel : Nat) :
    (run_indexed program mem input fuel).verdict =
      (run program mem input fuel).verdict ∧
    (run_indexed program mem input fuel).state =
      (run program mem input fuel).state := by
  rw [run_indexed_eq_run program mem input fuel hp hm]
  exact ⟨rfl, rfl⟩

end Leanisa.Proofs.I1c2.Checks
