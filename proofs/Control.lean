import Observations

namespace Leanisa.Proofs
open Sail Leanisa.Functions

def lowK (v : Word) : BitVec 64 := Sail.BitVec.extractLsb v 63 0

/-- Both branch outcomes of the ISA, including a changed frame on a taken jump. -/
def jumpState (s : machine_state) (condition destination frame : Word) : machine_state :=
  if lowK condition != 0 then ⟨lowK destination, lowK frame⟩ else advancedState s

theorem step_jump_of_reads {n : Nat} (mem : Vector Word n) (s : machine_state)
    (oc od ofp : BitVec 64) (vc vd vf : Word)
    (rc : read_memory mem (kmul s.fp oc) = ⟨vc, true⟩)
    (rd : read_memory mem (kmul s.fp od) = ⟨vd, true⟩)
    (rf : read_memory mem (kmul s.fp ofp) = ⟨vf, true⟩)
    (kc : in_k vc = true) (kd : in_k vd = true) (kf : in_k vf = true) :
    step s (.Jump (oc, od, ofp)) mem = ⟨jumpState s vc vd vf, .Running⟩ := by
  simp only [step, step_indexed, read_memory_indexed_empty, rc, rd, rf, kc, kd, kf]
  simp [jumpState, lowK, advancedState,
    show (status.Running == status.Running) = true from rfl]

/-- Unconditional K checks include destination and frame even on fallthrough.
No validity of the next PC is asserted: fetch/halting belongs to the runner. -/
inductive JumpStep {m : Nat} (s : machine_state) :
    PartialMemory m → instruction → PartialMemory m → machine_state → Prop where
  | checked {before after} (oc od ofp : BitVec 64) (c d f : Fin m) (vc vd vf : Word)
      (maps_c : kmul s.fp oc = gAddress c.val)
      (maps_d : kmul s.fp od = gAddress d.val)
      (maps_f : kmul s.fp ofp = gAddress f.val)
      (reads : Observed before [(c, vc), (d, vd), (f, vf)] after)
      (kc : in_k vc = true) (kd : in_k vd = true) (kf : in_k vf = true) :
      JumpStep s before (.Jump (oc, od, ofp)) after (jumpState s vc vd vf)

theorem JumpStep.evolves {m : Nat} {s next : machine_state}
    {before after : PartialMemory m} {ins}
    (operation : JumpStep s before ins after next) : Evolves before after := by
  cases operation with
  | checked oc od ofp c d f vc vd vf maps_c maps_d maps_f reads kc kd kf => exact reads.evolves

theorem JumpStep.simulates {m : Nat} (mem : Vector Word m) (domain : GPowerDomain m)
    {s next : machine_state} {before after later : PartialMemory m} {ins}
    (operation : JumpStep s before ins after next) (continuation : Evolves after later)
    (finished : Completes later (vectorImage mem)) :
    step s ins mem = ⟨next, .Running⟩ := by
  cases operation with
  | checked oc od ofp c d f vc vd vf maps_c maps_d maps_f reads kc kd kf =>
    apply step_jump_of_reads mem s oc od ofp vc vd vf
    · exact reads.lookup mem domain continuation finished c vc (by simp) _ maps_c
    · exact reads.lookup mem domain continuation finished d vd (by simp) _ maps_d
    · exact reads.lookup mem domain continuation finished f vf (by simp) _ maps_f
    · exact kc
    · exact kd
    · exact kf

end Leanisa.Proofs

#print axioms Leanisa.Proofs.JumpStep.simulates
