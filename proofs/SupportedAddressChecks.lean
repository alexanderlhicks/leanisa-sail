/-
Directed checks for supported finite address domains and whole-ISA policy
premises, including boundary sizes and effective-address equations.
-/
import SupportedWholeISA

noncomputable section
open Leanisa Leanisa.Proofs Leanisa.Proofs.Quotient Leanisa.Functions
namespace Leanisa.Proofs.Supported

theorem domain_empty : GPowerDomain 0 := supported_domain 0 (by decide)
theorem domain_singleton : GPowerDomain 1 := supported_domain 1 (by decide)
theorem domain_maximum : GPowerDomain (2^32) := supported_domain _ (by decide)

theorem maximum_address_nonzero : gAddress (2^32-1) ≠ 0#64 :=
  supported_nonzero _ (by decide)

theorem supported_endpoints_distinct : gAddress 0 ≠ gAddress (2^32-1) := by
  intro equal
  have h := domain_maximum.distinct ⟨0, by decide⟩ ⟨2^32-1, by decide⟩ equal
  have values := congrArg Fin.val h
  change 0 = 2^32-1 at values
  omega

theorem domain_cannot_be_unbounded : ¬GPowerDomain (2^64+1) := by
  intro domain
  have equal : gAddress 0 = gAddress (2^64) := by rfl
  have h := domain.distinct ⟨0, by decide⟩ ⟨2^64, by decide⟩ equal
  have values := congrArg Fin.val h
  change 0 = 2^64 at values
  omega

theorem canonical_zero_operand :
    (decode (encode (.Set (0, 0)))).isSome = true := by decide +kernel

theorem raw_zero_is_not_encoded_zero : (BitVec.ofNat 64 0) ≠ gAddress 0 := by
  rw [gAddress_origin]
  decide

theorem zero_pointer_passes_k_check : in_k (0#192) = true ∧ lowK (0#192) = 0#64 := by decide

theorem zero_pointer_has_no_supported_address (i : Nat) (bound : i < 2^32) :
    lowK (0#192) ≠ gAddress i := by
  change (0#64) ≠ gAddress i
  exact Ne.symm (supported_nonzero i bound)

theorem first_address_nonzero : gAddress 0 ≠ 0#64 := supported_nonzero 0 (by decide)

theorem actual_scan_first (mem : Vector Word (2^32)) :
    read_memory mem (gAddress 0) = ⟨mem.get ⟨0, by decide⟩, true⟩ :=
  supported_read mem (by decide) ⟨0, by decide⟩

theorem actual_scan_last (mem : Vector Word (2^32)) :
    read_memory mem (gAddress (2^32 - 1)) = ⟨mem.get ⟨2^32 - 1, by decide⟩, true⟩ :=
  supported_read mem (by decide) ⟨2^32 - 1, by decide⟩

theorem actual_fetch_first (program : Vector instruction (2^32)) :
    fetch program (gAddress 0) = some (program.get ⟨0, by decide⟩) :=
  supported_fetch program (by decide) ⟨0, by decide⟩

theorem actual_fetch_last (program : Vector instruction (2^32)) :
    fetch program (gAddress (2^32 - 1)) = some (program.get ⟨2^32 - 1, by decide⟩) :=
  supported_fetch program (by decide) ⟨2^32 - 1, by decide⟩

end Leanisa.Proofs.Supported
