import IndexedRunnerCore
import IndexedSupported

namespace Leanisa.Proofs
open Sail Leanisa.Functions

private theorem valid_of_indexed_guard_false {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256)
    (hp : 1 ≤ p)
    (guard : indexedInvalid program mem publicInput = false) :
    ValidInstance program mem publicInput := by
  simp only [indexedInvalid, Bool.or_eq_false_iff] at guard
  rcases guard with ⟨hpowp, hpowm, hlow, hupper, hpupper, hpublicLow, hpublicHigh⟩
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hpowp
  · simpa using hpowm
  · simpa using hlow
  · simpa using hupper
  · simpa using hpupper
  · simpa using hpublicLow
  · simpa using hpublicHigh

private theorem invalid_runners_equal {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel : Nat)
    (bad : indexedInvalid program mem publicInput = true) :
    run_indexed program mem publicInput fuel = run program mem publicInput fuel := by
  simp only [run_indexed, run, ← indexedInvalid_model program mem publicInput]
  simp [bad]

#print axioms Leanisa.Proofs.invalid_runners_equal

theorem indexed_initial_sentinel {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel : Nat)
    (good : indexedInvalid program mem publicInput = false)
    (atSentinel : initialState.pc = sentinel program) :
    run_indexed program mem publicInput fuel = ⟨initialState, .Halted⟩ := by
  simp only [run_indexed, ← indexedInvalid_model program mem publicInput, good,
    Bool.false_eq_true, ↓reduceIte]
  simp [initialState, sentinel] at atSentinel ⊢
  simp [atSentinel]
  rfl

#print axioms Leanisa.Proofs.indexed_initial_sentinel

theorem indexed_zero_fuel {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256)
    (good : indexedInvalid program mem publicInput = false)
    (notSentinel : initialState.pc ≠ sentinel program) :
    run_indexed program mem publicInput 0 = ⟨initialState, .OutOfFuel⟩ := by
  simp only [run_indexed, ← indexedInvalid_model program mem publicInput, good,
    Bool.false_eq_true, ↓reduceIte]
  simp [initialState, sentinel] at notSentinel ⊢
  simp [notSentinel]
  rfl

#print axioms Leanisa.Proofs.indexed_zero_fuel

private theorem active_runners_equal {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel : Nat)
    (good : indexedInvalid program mem publicInput = false)
    (notSentinel : initialState.pc ≠ sentinel program)
    (positive : fuel ≠ 0)
    (reads : ∀ a : BitVec 64,
      read_memory_indexed mem (build_address_index (if m ≥b p then m else p)) a =
        read_memory mem a)
    (fetches : ∀ a : BitVec 64,
      fetch_indexed program (build_address_index (if m ≥b p then m else p)) a =
        fetch program a) :
    run_indexed program mem publicInput fuel = run program mem publicInput fuel := by
  simp only [run_indexed, run, ← indexedInvalid_model program mem publicInput,
    good, Bool.false_eq_true, ↓reduceIte, Vector.length]
  have notSenBool : (1#64 == gpow (get_slice_int 64 ((p : Int) - 1) 0)) = false := by
    simpa [initialState, sentinel] using notSentinel
  have fuelBool : (fuel == 0) = false := by
    simpa using positive
  simp only [notSenBool, fuelBool]
  simp only [fetches, step_indexed_eq_step_of_reads mem
    (build_address_index (if m ≥b p then m else p)) reads]
  rfl

#print axioms Leanisa.Proofs.active_runners_equal

/-- Equality of the actual extracted runners from universal builder read and fetch equality.
The premises isolate the single genuine table used by the generated runner. -/
theorem run_indexed_eq_run_of_reads_fetches {p m : Nat}
    (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (fuel : Nat) (hp : 1 ≤ p)
    (reads : ∀ a : BitVec 64,
      read_memory_indexed mem (build_address_index (if m ≥b p then m else p)) a =
        read_memory mem a)
    (fetches : ∀ a : BitVec 64,
      fetch_indexed program (build_address_index (if m ≥b p then m else p)) a =
        fetch program a) :
    run_indexed program mem publicInput fuel = run program mem publicInput fuel := by
  cases hguard : indexedInvalid program mem publicInput with
  | true =>
      exact invalid_runners_equal program mem publicInput fuel hguard
  | false =>
      have valid : ValidInstance program mem publicInput :=
        valid_of_indexed_guard_false program mem publicInput hp hguard
      by_cases atSentinel : initialState.pc = sentinel program
      · calc
          run_indexed program mem publicInput fuel = ⟨initialState, .Halted⟩ :=
            indexed_initial_sentinel program mem publicInput fuel hguard atSentinel
          _ = run program mem publicInput fuel :=
            (indexed_ref_initial_sentinel program mem publicInput fuel valid atSentinel).symm
      · by_cases fuelZero : fuel = 0
        · subst fuel
          calc
            run_indexed program mem publicInput 0 = ⟨initialState, .OutOfFuel⟩ :=
              indexed_zero_fuel program mem publicInput hguard atSentinel
            _ = run program mem publicInput 0 :=
              (indexed_ref_zero_fuel program mem publicInput valid atSentinel).symm
        · exact active_runners_equal program mem publicInput fuel hguard atSentinel
            fuelZero reads fetches

#print axioms Leanisa.Proofs.run_indexed_eq_run_of_reads_fetches

/-- A covering builder table preserves every instruction result and state. -/
theorem step_indexed_build_eq_step {m N : Nat}
    (mem : Vector Word m) (covers : m ≤ N) (bound : N ≤ 2^32)
    (s : machine_state) (ins : instruction) :
    step_indexed s ins mem (build_address_index N) = step s ins mem := by
  exact step_indexed_eq_step_of_reads mem (build_address_index N)
    (fun address => I1c1.supported_read_memory_indexed_build_eq mem
      covers bound address) s ins

/-- The extracted Boolean size choice is the maximum of the two vector lengths. -/
theorem indexed_builder_size_eq_max (m p : Nat) :
    (if m ≥b p then m else p) = max m p := by
  by_cases h : p ≤ m
  · have hb : (m ≥b p) = true := by simpa using h
    simp [hb, Nat.max_eq_left h]
  · have hb : (m ≥b p) = false := by simpa using h
    have hmp : m ≤ p := Nat.le_of_lt (Nat.lt_of_not_ge h)
    simp [hb, Nat.max_eq_right hmp]

/-- Exact result and state equality for the generated indexed and scanning
    runners. The size and public-input checks are those of the extracted model;
    the two length premises match the declared Sail function domain. -/
theorem run_indexed_eq_run {p m : Nat}
    (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (fuel : Nat)
    (hp : 1 ≤ p) (_hm : 2 ≤ m) :
    run_indexed program mem publicInput fuel = run program mem publicInput fuel := by
  cases hguard : indexedInvalid program mem publicInput with
  | true =>
      exact invalid_runners_equal program mem publicInput fuel hguard
  | false =>
      have valid : ValidInstance program mem publicInput :=
        valid_of_indexed_guard_false program mem publicInput hp hguard
      have bound : max m p ≤ 2^32 := by
        have hmBound := valid.memoryUpper
        have hpBound := valid.programUpper
        omega
      apply run_indexed_eq_run_of_reads_fetches program mem publicInput fuel hp
      · intro address
        rw [indexed_builder_size_eq_max]
        exact I1c1.supported_read_memory_indexed_build_eq mem
          (Nat.le_max_left m p) bound address
      · intro address
        rw [indexed_builder_size_eq_max]
        exact I1c1.supported_fetch_indexed_build_eq program
          (Nat.le_max_right m p) bound address

#print axioms Leanisa.Proofs.run_indexed_eq_run
