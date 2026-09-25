import EncodedBlake

noncomputable section
open Leanisa Leanisa.Proofs Leanisa.Proofs.Quotient Leanisa.Functions Sail
namespace Leanisa.Proofs.Encoded

/-- The encoded natural offset zero is word one. Raw zero is different. -/
theorem encoded_zero : gAddress 0 = 1#64 := gAddress_origin

theorem raw_zero_differs : (0#64) ≠ gAddress 0 := by
  rw [encoded_zero]
  decide

/-- A canonical operand need not encode a natural offset. -/
theorem raw_zero_canonical : (decode (encode (.Set (0, 0)))).isSome = true := by
  decide +kernel

/-- Passing the K guard does not represent a pointer or a loaded destination. -/
theorem zero_passes_k : in_k (0#192) = true ∧ lowK (0#192) = 0#64 := by decide

theorem zero_unrepresented (i : Nat) (bound : i < 2^32) :
    lowK (0#192) ≠ gAddress i := by
  change (0#64) ≠ gAddress i
  exact Ne.symm (Supported.supported_nonzero i bound)

/-- Maximum finite target and zero offset use the public SET constructor. -/
theorem last_cell_set (s : machine_state) {before after : PartialMemory (2^32)}
    (value : Word) (frameRep : s.fp = gAddress (2^32 - 1))
    (assigned : assign before ⟨2^32 - 1, by decide⟩ value = some after) :
    IsaStep s before (.Set (gAddress 0, value)) after (advancedState s) [] := by
  apply encoded_set s (2^32 - 1) 0 ⟨2^32 - 1, by decide⟩ value
    (by decide) frameRep
  · decide
  · exact assigned

/-- Both cells can be accessed when the adjacent pair ends at the last cell. -/
theorem last_adjacent_pair :
    advance (kmul (gAddress (2^32 - 2)) (gAddress 0)) = gAddress (2^32 - 1) := by
  apply encoded_adjacent (gAddress (2^32 - 2)) (gAddress 0)
    (2^32 - 2) 0 (⟨2^32 - 2, by decide⟩ : Fin (2^32))
    (⟨2^32 - 1, by decide⟩ : Fin (2^32))
    (by decide) rfl rfl <;> decide

/-- The final cell has no finite successor, despite its own valid access. -/
theorem no_next_after_last :
    ¬ ∃ next : Fin (2^32), next.val = (2^32 - 1) + 1 := by
  intro ⟨next, h⟩
  have := next.isLt
  omega

/-- The strict addition and recurrence bounds cannot be removed. -/
theorem wrapped_recurrence_false :
    gAddress ((2^64 - 1) + 1) ≠ advance (gAddress (2^64 - 1)) := by
  rw [show (2^64 - 1) + 1 = (2^64 : Nat) by decide,
    show gAddress (2^64) = 1#64 from sail_gpow_zero,
    show gAddress (2^64 - 1) = 1#64 from sail_gpow_all_ones]
  decide

theorem wrapped_addition_false :
    kmul (gAddress (2^64 - 1)) (gAddress 1) ≠
      gAddress ((2^64 - 1) + 1) := by
  rw [show (2^64 - 1) + 1 = (2^64 : Nat) by decide,
    show gAddress (2^64 - 1) = 1#64 from sail_gpow_all_ones,
    gAddress_one, show gAddress (2^64) = 1#64 from sail_gpow_zero,
    kmul_one_left]
  decide

/-- At PC zero in a two-position program, Pc-mode stores index two. -/
theorem pc_plus_two_beyond_program : 2 ≤ (0 + 2 : Nat) ∧
    derefValue ⟨gAddress 0, gAddress 0⟩ .Pc (0 : Word) = embed_k (gAddress 2) := by
  constructor
  · decide
  · exact deref_pc_value _ 0 0 rfl (by decide)

end Leanisa.Proofs.Encoded
