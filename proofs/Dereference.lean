import Control

namespace Leanisa.Proofs
open Sail Leanisa.Functions

def derefValue (s : machine_state) (mode : deref_mode) (source : Word) : Word :=
  match mode with
  | .Cell => source
  | .Pc => embed_k (advance (advance s.pc))
  | .Fp => embed_k s.fp

theorem step_deref_of_reads {n : Nat} (mem : Vector Word n) (s : machine_state)
    (o1 o2 o3 : BitVec 64) (mode : deref_mode) (pointer source : Word)
    (rp : read_memory mem (kmul s.fp o1) = ⟨pointer, true⟩)
    (rs : read_memory mem (kmul s.fp o3) = ⟨source, true⟩)
    (rt : read_memory mem (kmul (lowK pointer) o2) = ⟨derefValue s mode source, true⟩)
    (kp : in_k pointer = true) :
    step s (.Deref (o1, o2, o3, mode)) mem = ⟨advancedState s, .Running⟩ := by
  simp only [lowK] at rt
  cases mode <;>
    simp only [derefValue] at rt <;>
    simp [step, step_indexed, read_memory_indexed_empty, rp, rs, rt,
      kp, advancedState,
      show (status.Running == status.Running) = true from rfl]

/-- Cell mode records an equality, without defaulting either endpoint to zero.
Pc/Fp modes assign the target. The syntactic source is bounded in every mode. -/
inductive DerefStep {m : Nat} (s : machine_state) :
    PartialMemory m → instruction → PartialMemory m → List (Fin m × Fin m) → Prop where
  | cell {before observed} (o1 o2 o3 : BitVec 64) (p source target : Fin m) (pointer : Word)
      (maps_p : kmul s.fp o1 = gAddress p.val)
      (maps_s : kmul s.fp o3 = gAddress source.val)
      (maps_t : kmul (lowK pointer) o2 = gAddress target.val)
      (read : Observed before [(p, pointer)] observed)
      (kp : in_k pointer = true) :
      DerefStep s before (.Deref (o1, o2, o3, .Cell)) observed [(target, source)]
  | stored {before observed after} (o1 o2 o3 : BitVec 64) (mode : deref_mode)
      (p source target : Fin m) (pointer : Word) (notCell : mode ≠ .Cell)
      (maps_p : kmul s.fp o1 = gAddress p.val)
      (maps_s : kmul s.fp o3 = gAddress source.val)
      (maps_t : kmul (lowK pointer) o2 = gAddress target.val)
      (read : Observed before [(p, pointer)] observed)
      (kp : in_k pointer = true)
      (write : assign observed target (derefValue s mode 0) = some after) :
      DerefStep s before (.Deref (o1, o2, o3, mode)) after []

theorem DerefStep.evolves {m : Nat} {s : machine_state}
    {before after : PartialMemory m} {ins pending}
    (operation : DerefStep s before ins after pending) : Evolves before after := by
  cases operation with
  | cell o1 o2 o3 p source target pointer maps_p maps_s maps_t read kp => exact read.evolves
  | stored o1 o2 o3 mode p source target pointer notCell maps_p maps_s maps_t read kp write =>
    exact .trans read.evolves (.assignment target _ write)

theorem DerefStep.simulates {m : Nat} (mem : Vector Word m) (domain : GPowerDomain m)
    {s : machine_state} {before after later : PartialMemory m} {ins pending}
    (operation : DerefStep s before ins after pending) (continuation : Evolves after later)
    (finished : Completes later (vectorImage mem))
    (resolved : Resolves pending (vectorImage mem)) :
    step s ins mem = ⟨advancedState s, .Running⟩ := by
  cases operation with
  | cell o1 o2 o3 p source target pointer maps_p maps_s maps_t read kp =>
    have equal : mem.get target = mem.get source := resolved (target, source) (by simp)
    apply step_deref_of_reads mem s o1 o2 o3 .Cell pointer (mem.get source)
    · exact read.lookup mem domain continuation finished p pointer (by simp) _ maps_p
    · rw [maps_s]; exact read_memory_gAddress mem domain source
    · rw [maps_t, read_memory_gAddress mem domain target, equal]; rfl
    · exact kp
  | stored o1 o2 o3 mode p source target pointer notCell maps_p maps_s maps_t read kp write =>
    have pointerRead := read.lookup mem domain
      (.trans (.assignment target _ write) continuation) finished p pointer (by simp) _ maps_p
    have targetRead := completed_cell_lookup mem domain finished target _
      (execution_extends continuation _ _ (assign_fixes_value write)) _ maps_t
    have value : derefValue s mode 0 = derefValue s mode (mem.get source) := by
      cases mode <;> simp_all [derefValue]
    apply step_deref_of_reads mem s o1 o2 o3 mode pointer (mem.get source)
    · exact pointerRead
    · rw [maps_s]; exact read_memory_gAddress mem domain source
    · simpa only [value] using targetRead
    · exact kp

end Leanisa.Proofs

#print axioms Leanisa.Proofs.DerefStep.simulates
