import EncodedChecks

noncomputable section
open Leanisa Leanisa.Proofs Leanisa.Proofs.Quotient Leanisa.Functions Sail
namespace Leanisa.Proofs.Encoded

private def pointerMemory : PartialMemory 2 := fun i => if i = 0 then some (1 : Word) else none

private theorem pointerObserved : Observed pointerMemory
    [((0 : Fin 2), (1 : Word))] pointerMemory := by
  have h : observeZero pointerMemory (0 : Fin 2) = (1, pointerMemory) := by
    simp [pointerMemory, observeZero]
  simpa [h] using Observed.cons pointerMemory (0 : Fin 2) (Observed.nil pointerMemory)

/-- Pc mode stores PC+2, here outside a two-position program, while source is bounded. -/
theorem pc_stored_example :
    IsaStep initialState pointerMemory
      (.Deref (gAddress 0, gAddress 1, gAddress 0, .Pc))
      (fun i => if i = (1 : Fin 2) then some (embed_k (gAddress 2)) else pointerMemory i)
      (advancedState initialState) [] := by
  let after : PartialMemory 2 := fun i => if i = 1 then some (embed_k (gAddress 2)) else pointerMemory i
  have write : assign pointerMemory (1 : Fin 2) (embed_k (gAddress 2)) = some after := by
    simp [assign, pointerMemory, after]
  exact encoded_deref_pc initialState 0 0 0 1 0 0 (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) 1
    (by decide) (by simp [initialState, gAddress_origin])
    (by simp [initialState, gAddress_origin]) (by decide)
    (by decide) (by decide) (by decide)
    (by rw [gAddress_origin]; decide) pointerObserved (by decide) write

/-- Fp mode stores the represented frame with the same bounded source read. -/
theorem fp_stored_example :
    IsaStep initialState pointerMemory
      (.Deref (gAddress 0, gAddress 1, gAddress 0, .Fp))
      (fun i => if i = (1 : Fin 2) then some (embed_k (gAddress 0)) else pointerMemory i)
      (advancedState initialState) [] := by
  let after : PartialMemory 2 := fun i => if i = 1 then some (embed_k (gAddress 0)) else pointerMemory i
  have write : assign pointerMemory (1 : Fin 2) (embed_k (gAddress 0)) = some after := by
    simp [assign, pointerMemory, after]
  exact encoded_deref_fp initialState 0 0 1 0 0 (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) 1
    (by decide) (by simp [initialState, gAddress_origin])
    (by decide) (by decide) (by decide)
    (by rw [gAddress_origin]; decide) pointerObserved (by decide) write

end Leanisa.Proofs.Encoded
