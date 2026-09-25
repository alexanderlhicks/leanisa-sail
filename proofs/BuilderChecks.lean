import BuilderSupported

namespace Leanisa.Proofs.I1b.Checks
open Leanisa.Functions Leanisa.Proofs Leanisa.Proofs.I1a

theorem empty_lookup (a : BitVec 64) :
    lookup_address (build_address_index 0) a = none := by
  apply (supported_build_lookup_none_iff 0 (by omega) a).2
  intro i
  exact Fin.elim0 i

theorem singleton_results :
    lookup_address (build_address_index 1) 1 = some 0 ∧
    lookup_address (build_address_index 1) 0 = none ∧
    lookup_address (build_address_index 1) 2 = none := by
  decide +kernel

theorem three_results :
    lookup_address (build_address_index 3) 1 = some 0 ∧
    lookup_address (build_address_index 3) 2 = some 1 ∧
    lookup_address (build_address_index 3) 4 = some 2 ∧
    lookup_address (build_address_index 3) 8 = none := by
  decide +kernel

theorem collision_chain :
    startSlot 16 (gAddress 4) = 0 ∧
    startSlot 16 (gAddress 5) = 0 ∧
    startSlot 16 (gAddress 7) = 0 ∧
    address_slot (build_address_index 8) (gAddress 7) = some 6 ∧
    lookup_address (build_address_index 8) (gAddress 7) = some 7 := by
  decide +kernel

/-- Logical false control for silently skipping the final insertion. -/
theorem cannot_skip_last :
    ¬ lookup_address (build_address_index 1) 1 = none := by
  have h := singleton_results.1
  intro bad
  rw [bad] at h
  cases h

/-- Logical false control for writing an incorrect offset. -/
theorem cannot_shift_offset :
    ¬ lookup_address (build_address_index 1) 1 = some 1 := by
  have h := singleton_results.1
  intro bad
  rw [bad] at h
  cases h

/-- A forged table can contain the key after a hole in its probe path. -/
def forgedHole : Vector address_entry 3 :=
  #v[⟨1#64, 0⟩, emptyEntry, emptyEntry]

theorem forged_hole_results :
    (forgedHole[0]!).address = 1#64 ∧
    lookup_address forgedHole 1 = none := by
  decide +kernel

theorem membership_alone_is_insufficient :
    ¬ (∀ table : Vector address_entry 3,
      (∃ slot : Fin 3, (table.get slot).address = 1#64) →
      lookup_address table 1 = some 0) := by
  intro falseClaim
  have present : ∃ slot : Fin 3, (forgedHole.get slot).address = 1#64 := by
    exact ⟨⟨0, by decide⟩, by decide⟩
  have h := falseClaim forgedHole present
  rw [forged_hole_results.2] at h
  cases h

theorem maximal_source_arithmetic :
    2 * (2^32 : Nat) = 2^33 ∧
    2^32 - 1 ≤ 4294967295 ∧
    2^33 - 1 ≤ 8589934591 := by
  constructor
  · norm_num
  constructor <;> norm_num

end Leanisa.Proofs.I1b.Checks
