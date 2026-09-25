import IndexedCorrectness
import SupportedAddressDomain

namespace Leanisa.Proofs.I1c1
open Sail Leanisa.Functions Leanisa.Proofs

/-- A genuine source-sized index agrees with the extracted memory scan at
    every address, for every covered memory vector. -/
theorem supported_read_memory_indexed_build_eq {n N : Nat}
    (mem : Vector Word n) (covers : n ≤ N) (sizeBound : N ≤ 2^32)
    (address : BitVec 64) :
    read_memory_indexed mem (build_address_index N) address =
      read_memory mem address := by
  exact read_memory_indexed_build_eq mem covers (by omega)
    (Supported.supported_domain N sizeBound)
    (fun i => Supported.supported_nonzero i.val
      (by have := i.isLt; omega)) address

/-- A genuine source-sized index agrees with the extracted instruction scan
    at every address, for every covered program vector. -/
theorem supported_fetch_indexed_build_eq {n N : Nat}
    (program : Vector Leanisa.instruction n)
    (covers : n ≤ N) (sizeBound : N ≤ 2^32)
    (address : BitVec 64) :
    fetch_indexed program (build_address_index N) address =
      fetch program address := by
  exact fetch_indexed_build_eq program covers (by omega)
    (Supported.supported_domain N sizeBound)
    (fun i => Supported.supported_nonzero i.val
      (by have := i.isLt; omega)) address

end Leanisa.Proofs.I1c1
