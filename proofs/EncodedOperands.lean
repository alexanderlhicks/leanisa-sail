import SupportedWholeISA

noncomputable section
open Leanisa Leanisa.Proofs Leanisa.Proofs.Quotient Leanisa.Functions
namespace Leanisa.Proofs.Encoded

/-- A finite target supplies the strict bound needed by actual 64-bit addition. -/
theorem encoded_access {m : Nat} (baseWord operand : BitVec 64) (base offset : Nat)
    (target : Fin m) (bound : m ≤ 2^32)
    (baseRep : baseWord = gAddress base) (operandRep : operand = gAddress offset)
    (targetIndex : target.val = base + offset) :
    kmul baseWord operand = gAddress target.val := by
  rw [baseRep, operandRep, targetIndex]
  exact gAddress_add base offset (by have h := target.isLt; omega)

/-- The second bounded cell supplies the separate non-wrap successor bound. -/
theorem encoded_adjacent {m : Nat} (baseWord operand : BitVec 64) (base offset : Nat)
    (target next : Fin m) (bound : m ≤ 2^32)
    (baseRep : baseWord = gAddress base) (operandRep : operand = gAddress offset)
    (targetIndex : target.val = base + offset) (nextIndex : next.val = target.val + 1) :
    advance (kmul baseWord operand) = gAddress next.val := by
  rw [encoded_access baseWord operand base offset target bound baseRep operandRep targetIndex,
    nextIndex]
  exact (gAddress_successor target.val (by have h := next.isLt; omega)).symm

/-- PC progression needs a strict encoding bound, independently of `in_k`. -/
theorem represented_advance (s : machine_state) (pcIndex : Nat)
    (pcRep : s.pc = gAddress pcIndex) (bound : pcIndex + 1 < 2^64) :
    (advancedState s).pc = gAddress (pcIndex + 1) := by
  simpa [advancedState, pcRep] using (gAddress_successor pcIndex bound).symm

/-- DEREF Pc stores the twice-advanced represented PC. It may be outside the program. -/
theorem deref_pc_value (s : machine_state) (pcIndex : Nat) (source : Word)
    (pcRep : s.pc = gAddress pcIndex) (bound : pcIndex + 2 < 2^64) :
    derefValue s .Pc source = embed_k (gAddress (pcIndex + 2)) := by
  simp only [derefValue, pcRep]
  rw [← gAddress_successor pcIndex (by omega),
    ← gAddress_successor (pcIndex + 1) (by omega)]

/-- DEREF Fp stores the represented frame. -/
theorem deref_fp_value (s : machine_state) (frame : Nat) (source : Word)
    (frameRep : s.fp = gAddress frame) :
    derefValue s .Fp source = embed_k (gAddress frame) := by
  simp only [derefValue, frameRep]

end Leanisa.Proofs.Encoded
