import Instructions

namespace Leanisa.Proofs
open Leanisa.Functions

/-- A batch of eager reads in their execution order. Values are fixed at the
instant of observation, including repeated addresses and initially unset cells. -/
inductive Observed {n : Nat} : PartialMemory n → List (Fin n × Word) → PartialMemory n → Prop where
  | nil (memory) : Observed memory [] memory
  | cons (memory : PartialMemory n) (a : Fin n) {tail after}
      (rest : Observed (observeZero memory a).2 tail after) :
      Observed memory ((a, (observeZero memory a).1) :: tail) after

theorem Observed.evolves {n : Nat} {before after : PartialMemory n} {reads}
    (observed : Observed before reads after) : Evolves before after := by
  induction observed with
  | nil memory => exact .refl memory
  | cons memory a rest ih => exact .trans (.observation memory a) ih

theorem Observed.fixed {n : Nat} {before after : PartialMemory n} {reads}
    (observed : Observed before reads after) (a : Fin n) (v : Word)
    (member : (a, v) ∈ reads) : after a = some v := by
  induction observed with
  | nil memory => simp at member
  | cons memory address rest ih =>
    simp only [List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | member
    · exact execution_extends rest.evolves _ _ (observe_fixes_value memory a)
    · exact ih member

theorem Observed.lookup {n : Nat} (mem : Vector Word n) (domain : GPowerDomain n)
    {before after later : PartialMemory n} {reads}
    (observed : Observed before reads after) (execution : Evolves after later)
    (finished : Completes later (vectorImage mem)) (a : Fin n) (v : Word)
    (member : (a, v) ∈ reads) (address : BitVec 64) (maps : address = gAddress a.val) :
    read_memory mem address = ⟨v, true⟩ := by
  exact completed_cell_lookup mem domain finished a v
    (execution_extends execution a v (observed.fixed a v member)) address maps

end Leanisa.Proofs
