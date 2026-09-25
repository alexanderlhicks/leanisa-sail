import EncodedArithmeticControl

noncomputable section
open Leanisa Leanisa.Proofs Leanisa.Functions Sail
namespace Leanisa.Proofs.Encoded

/-- Cell mode records deferred target/source equality without forcing either cell. -/
theorem encoded_deref_cell {m : Nat} (s : machine_state) (frame o1 o2 o3 pointerBase : Nat)
    (pointerCell source target : Fin m) (pointer : Word)
    {before observed : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (pointerIndex : pointerCell.val = frame + o1)
    (sourceIndex : source.val = frame + o3)
    (targetIndex : target.val = pointerBase + o2)
    (pointerRep : lowK pointer = gAddress pointerBase)
    (read : Observed before [(pointerCell, pointer)] observed)
    (kp : in_k pointer = true) :
    IsaStep s before (.Deref (gAddress o1, gAddress o2, gAddress o3, .Cell))
      observed (advancedState s) [(target, source)] := by
  exact .deref (.cell (gAddress o1) (gAddress o2) (gAddress o3)
    pointerCell source target pointer
    (encoded_access s.fp (gAddress o1) frame o1 pointerCell bound frameRep rfl pointerIndex)
    (encoded_access s.fp (gAddress o3) frame o3 source bound frameRep rfl sourceIndex)
    (encoded_access (lowK pointer) (gAddress o2) pointerBase o2 target bound pointerRep rfl targetIndex)
    read kp)

/-- Pc mode keeps bounded syntactic source access and stores represented PC+2. -/
theorem encoded_deref_pc {m : Nat} (s : machine_state)
    (frame pcIndex o1 o2 o3 pointerBase : Nat)
    (pointerCell source target : Fin m) (pointer : Word)
    {before observed after : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (pcRep : s.pc = gAddress pcIndex) (pcBound : pcIndex + 2 < 2^64)
    (pointerIndex : pointerCell.val = frame + o1)
    (sourceIndex : source.val = frame + o3)
    (targetIndex : target.val = pointerBase + o2)
    (pointerRep : lowK pointer = gAddress pointerBase)
    (read : Observed before [(pointerCell, pointer)] observed)
    (kp : in_k pointer = true)
    (write : assign observed target (embed_k (gAddress (pcIndex + 2))) = some after) :
    IsaStep s before (.Deref (gAddress o1, gAddress o2, gAddress o3, .Pc))
      after (advancedState s) [] := by
  have stored : assign observed target (derefValue s .Pc 0) = some after := by
    simpa only [deref_pc_value s pcIndex 0 pcRep pcBound] using write
  exact .deref (.stored (gAddress o1) (gAddress o2) (gAddress o3) .Pc
    pointerCell source target pointer (by intro h; cases h)
    (encoded_access s.fp (gAddress o1) frame o1 pointerCell bound frameRep rfl pointerIndex)
    (encoded_access s.fp (gAddress o3) frame o3 source bound frameRep rfl sourceIndex)
    (encoded_access (lowK pointer) (gAddress o2) pointerBase o2 target bound pointerRep rfl targetIndex)
    read kp stored)

/-- Fp mode stores the represented frame and retains bounded syntactic source access. -/
theorem encoded_deref_fp {m : Nat} (s : machine_state)
    (frame o1 o2 o3 pointerBase : Nat)
    (pointerCell source target : Fin m) (pointer : Word)
    {before observed after : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (pointerIndex : pointerCell.val = frame + o1)
    (sourceIndex : source.val = frame + o3)
    (targetIndex : target.val = pointerBase + o2)
    (pointerRep : lowK pointer = gAddress pointerBase)
    (read : Observed before [(pointerCell, pointer)] observed)
    (kp : in_k pointer = true)
    (write : assign observed target (embed_k (gAddress frame)) = some after) :
    IsaStep s before (.Deref (gAddress o1, gAddress o2, gAddress o3, .Fp))
      after (advancedState s) [] := by
  have stored : assign observed target (derefValue s .Fp 0) = some after := by
    simpa only [deref_fp_value s frame 0 frameRep] using write
  exact .deref (.stored (gAddress o1) (gAddress o2) (gAddress o3) .Fp
    pointerCell source target pointer (by intro h; cases h)
    (encoded_access s.fp (gAddress o1) frame o1 pointerCell bound frameRep rfl pointerIndex)
    (encoded_access s.fp (gAddress o3) frame o3 source bound frameRep rfl sourceIndex)
    (encoded_access (lowK pointer) (gAddress o2) pointerBase o2 target bound pointerRep rfl targetIndex)
    read kp stored)

end Leanisa.Proofs.Encoded
