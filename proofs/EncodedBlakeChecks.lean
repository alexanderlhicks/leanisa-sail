import EncodedModeChecks

noncomputable section
open Leanisa Leanisa.Proofs Leanisa.Proofs.Quotient Leanisa.Functions Sail
namespace Leanisa.Proofs.Encoded

private def chunkInputs : PartialMemory 4 :=
  fun i => if i.val < 2 then some (0 : Word) else none

/-- Repeated input cells, both adjacent pairs, and two real compatible writes. -/
theorem blake_repeated_inputs :
    ∃ after : PartialMemory 4,
      IsaStep initialState chunkInputs
        (.Blake2s (gAddress 0, gAddress 0, gAddress 0, gAddress 0,
          gAddress 0, gAddress 2, gAddress 0))
        after (advancedState initialState) [] := by
  let low : Word := compressionLow 0 0 0 0 0 0 0
  let high : Word := compressionHigh 0 0 0 0 0 0 0
  let middle : PartialMemory 4 := fun i => if i = 2 then some low else chunkInputs i
  let after : PartialMemory 4 := fun i => if i = 3 then some high else middle i
  have reads : Observed chunkInputs
      [((0 : Fin 4), 0), (0, 0), (0, 0), (0, 0), (0, 0), (1, 0), (0, 0)]
      chunkInputs := by
    simpa using observed_known chunkInputs
      ([(0 : Fin 4), 0, 0, 0, 0, 1, 0]) 0 (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with h | h | h | h | h | h | h <;> subst i <;> simp [chunkInputs])
  have w0 : assign chunkInputs (2 : Fin 4) low = some middle := by
    simp [assign, chunkInputs, middle]
  have w1 : assign middle (3 : Fin 4) high = some after := by
    simp [assign, chunkInputs, middle, after]
  refine ⟨after, ?_⟩
  exact encoded_blake initialState 0 0 0 0 0 0 2 0
    (0 : Fin 4) (0 : Fin 4) (0 : Fin 4) (0 : Fin 4)
    (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4) (0 : Fin 4)
    0 0 0 0 0 0 0 (by decide)
    (by simp [initialState, gAddress_origin])
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    reads (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) w0 w1

/-- Output cell zero may alias the first input only when the observed value
agrees with the actual compression output. The checked policy still permits it. -/
theorem blake_input_output_alias
    (m0 m1 m2 m3 cv0 cv1 md : Word)
    {before observed middle after : PartialMemory 4}
    (reads : Observed before
      [((0 : Fin 4), m0), (0, m1), (0, m2), (0, m3),
        (2, cv0), (3, cv1), (0, md)] observed)
    (c0 : in_chunk m0 = true) (c1 : in_chunk m1 = true)
    (c2 : in_chunk m2 = true) (c3 : in_chunk m3 = true)
    (cc0 : in_chunk cv0 = true) (cc1 : in_chunk cv1 = true)
    (cmd : in_chunk md = true)
    (write0 : assign observed (0 : Fin 4)
      (compressionLow m0 m1 m2 m3 cv0 cv1 md) = some middle)
    (write1 : assign middle (1 : Fin 4)
      (compressionHigh m0 m1 m2 m3 cv0 cv1 md) = some after) :
    m0 = compressionLow m0 m1 m2 m3 cv0 cv1 md ∧
    IsaStep initialState before
      (.Blake2s (gAddress 0, gAddress 0, gAddress 0, gAddress 0,
        gAddress 2, gAddress 0, gAddress 0))
      after (advancedState initialState) [] := by
  have fixed : observed (0 : Fin 4) = some m0 :=
    reads.fixed (0 : Fin 4) m0 (by simp)
  have compatible : m0 = compressionLow m0 m1 m2 m3 cv0 cv1 md := by
    by_contra neq
    have failed : assign observed (0 : Fin 4)
        (compressionLow m0 m1 m2 m3 cv0 cv1 md) = none := by
      simp [assign, fixed, neq]
    rw [failed] at write0
    cases write0
  refine ⟨compatible, ?_⟩
  exact encoded_blake initialState 0 0 0 0 0 2 0 0
    (0 : Fin 4) (0 : Fin 4) (0 : Fin 4) (0 : Fin 4)
    (2 : Fin 4) (3 : Fin 4) (0 : Fin 4) (1 : Fin 4) (0 : Fin 4)
    m0 m1 m2 m3 cv0 cv1 md (by decide)
    (by simp [initialState, gAddress_origin])
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    reads c0 c1 c2 c3 cc0 cc1 cmd write0 write1

end Leanisa.Proofs.Encoded
