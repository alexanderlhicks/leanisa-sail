import Runner
import IndexedStep

namespace Leanisa.Proofs
open Sail Leanisa.Functions

/-- The common generated instance guard, named so both runners can be reduced
    through the same Boolean expression. -/
def indexedInvalid {p m : Nat} (_program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) : Bool :=
    (!power_of_two p) || ((!power_of_two m) || ((m <b 65536) ||
    ((m >b 4294967296) || ((p >b 4294967296) ||
    ((mem[0]! != (0#64 +++ Sail.BitVec.extractLsb publicInput 127 0)) ||
    (mem[1]! != (0#64 +++ Sail.BitVec.extractLsb publicInput 255 128)))))))

theorem indexedInvalid_model {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) :
    indexedInvalid program mem publicInput =
      ((! (power_of_two (Vector.length program))) || ((! (power_of_two (Vector.length mem))) || (((Vector.length
               mem) <b 65536) || (((Vector.length mem) >b 4294967296) || (((Vector.length program) >b 4294967296) || (((GetElem?.getElem!
                     mem 0) != (0x0000000000000000#64 +++ (Sail.BitVec.extractLsb publicInput 127 0))) || ((GetElem?.getElem!
                     mem 1) != (0x0000000000000000#64 +++ (Sail.BitVec.extractLsb publicInput 255
                       128))))))))) := by
  rfl

#print axioms Leanisa.Proofs.indexedInvalid_model

theorem indexed_ref_initial_sentinel {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel : Nat)
    (valid : ValidInstance program mem publicInput)
    (atSentinel : initialState.pc = sentinel program) :
    run program mem publicInput fuel = ⟨initialState, .Halted⟩ := by
  let states : Nat → machine_state := fun _ => initialState
  have trace : StepTrace program mem states 0 := by
    refine ⟨rfl, ?_, atSentinel⟩
    intro i hi
    omega
  simpa only [states, initialState, beq_self_eq_true, ↓reduceIte] using
    run_trace_terminal program mem publicInput fuel 0 valid states trace (by omega)

theorem indexed_ref_zero_fuel {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256)
    (valid : ValidInstance program mem publicInput)
    (notSentinel : initialState.pc ≠ sentinel program) :
    run program mem publicInput 0 = ⟨initialState, .OutOfFuel⟩ := by
  let states : Nat → machine_state := fun _ => initialState
  have chain : StepPrefix program mem states 0 := by
    refine ⟨rfl, ?_⟩
    intro i hi
    omega
  simpa only [states] using
    run_prefix_out_of_fuel program mem publicInput 0 0 valid states chain
      (by omega) notSentinel

#print axioms Leanisa.Proofs.indexed_ref_initial_sentinel
#print axioms Leanisa.Proofs.indexed_ref_zero_fuel
