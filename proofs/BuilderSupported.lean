import BuilderCorrectness
import SupportedAddressDomain

namespace Leanisa.Proofs.I1b
open Leanisa.Proofs

/-- The supported arithmetic domain discharges the builder's explicit
    generator and nonzero obligations. -/
theorem supported_build_lookup_some_iff (size : Nat)
    (sizeBound : size ≤ 2^32) (address : BitVec 64) (offset : Nat) :
    Leanisa.Functions.lookup_address
        (Leanisa.Functions.build_address_index size) address = some offset ↔
      offset < size ∧ address = gAddress offset := by
  exact build_index_lookup_some_iff size (by omega)
    (Supported.supported_domain size sizeBound)
    (fun i => Supported.supported_nonzero i.val (by have := i.isLt; omega))
    address offset

theorem supported_build_lookup_none_iff (size : Nat)
    (sizeBound : size ≤ 2^32) (address : BitVec 64) :
    Leanisa.Functions.lookup_address
        (Leanisa.Functions.build_address_index size) address = none ↔
      ∀ i : Fin size, address ≠ gAddress i.val := by
  exact build_index_lookup_none_iff size (by omega)
    (Supported.supported_domain size sizeBound)
    (fun i => Supported.supported_nonzero i.val (by have := i.isLt; omega))
    address

theorem supported_build_lookup_hit (size : Nat)
    (sizeBound : size ≤ 2^32) (i : Fin size) :
    Leanisa.Functions.lookup_address
        (Leanisa.Functions.build_address_index size) (gAddress i.val) =
      some i.val := by
  exact (supported_build_lookup_some_iff size sizeBound (gAddress i.val) i.val).2
    ⟨i.isLt, rfl⟩

theorem supported_build_lookup_miss (size : Nat)
    (sizeBound : size ≤ 2^32) (address : BitVec 64)
    (absent : ∀ i : Fin size, address ≠ gAddress i.val) :
    Leanisa.Functions.lookup_address
        (Leanisa.Functions.build_address_index size) address = none :=
  (supported_build_lookup_none_iff size sizeBound address).2 absent

end Leanisa.Proofs.I1b
