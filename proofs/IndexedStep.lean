import Instructions

namespace Leanisa.Proofs
open Sail Leanisa.Functions

/-- Full extracted step congruence from all-address indexed read equality. -/
theorem step_indexed_eq_step_of_reads {m C : Nat}
    (mem : Vector Word m) (index : Vector address_entry C)
    (reads : ∀ a : BitVec 64,
      read_memory_indexed mem index a = read_memory mem a)
    (s : machine_state) (ins : instruction) :
    step_indexed s ins mem index = step s ins mem := by
  cases ins <;> simp only [step, step_indexed, read_memory_indexed_empty, reads]

#print axioms Leanisa.Proofs.step_indexed_eq_step_of_reads
