import IndexedCases

namespace Leanisa.Proofs.I1c1
open Sail Leanisa.Functions Leanisa.Proofs Leanisa.Proofs.I1b

theorem absent_shorter {n N : Nat} (domain : GPowerDomain N)
    (covers : n ≤ N) (offset : Nat) (hoffset : offset < N)
    (outside : n ≤ offset) :
    ∀ i : Fin n, gAddress offset ≠ gAddress i.val := by
  intro i heq
  have hiN : i.val < N := Nat.lt_of_lt_of_le i.isLt covers
  have hsame := domain.distinct (⟨offset, hoffset⟩ : Fin N)
    (⟨i.val, hiN⟩ : Fin N) heq
  have hval : offset = i.val := congrArg (fun x : Fin N => x.val) hsame
  have hi := i.isLt
  omega

/-- Exact equality for every address and all memory contents, using the
    genuine extracted builder and the conditional generator contract. -/
theorem read_memory_indexed_build_eq {n N : Nat} (mem : Vector Word n)
    (covers : n ≤ N) (sizeBound : N ≤ 4294967296)
    (domain : GPowerDomain N)
    (nonzero : ∀ i : Fin N, gAddress i.val ≠ 0#64)
    (address : BitVec 64) :
    read_memory_indexed mem (build_address_index N) address =
      read_memory mem address := by
  by_cases hzero : N = 0
  · subst N
    have hn : n = 0 := by omega
    subst n
    exact read_indexed_empty_fallback mem (build_address_index 0) address
  have hcapacity : 0 < 2 * N := by omega
  have scanDomain := GPowerDomain.restrict domain covers
  cases hlookup : lookup_address (build_address_index N) address with
  | none =>
    have hnone := (build_index_lookup_none_iff N sizeBound domain nonzero address).mp hlookup
    have hmiss : ∀ i : Fin n, address ≠ gAddress i.val := by
      intro i
      exact hnone ⟨i.val, by omega⟩
    rw [read_indexed_lookup_none mem (build_address_index N) hcapacity address hlookup,
      read_memory_miss mem scanDomain address hmiss]
  | some offset =>
    obtain ⟨hltN, haddress⟩ :=
      (build_index_lookup_some_iff N sizeBound domain nonzero address offset).mp hlookup
    by_cases hlt : offset < n
    · rw [read_indexed_hit mem (build_address_index N) hcapacity address offset
        hlookup hlt, haddress]
      exact (read_memory_gAddress mem scanDomain ⟨offset, hlt⟩).symm
    · have hout : n ≤ offset := by omega
      have hmiss : ∀ i : Fin n, address ≠ gAddress i.val := by
        intro i
        rw [haddress]
        exact absent_shorter domain covers offset hltN hout i
      rw [read_indexed_out_of_range mem (build_address_index N) hcapacity
        address offset hlookup hout, read_memory_miss mem scanDomain address hmiss]

theorem fetch_indexed_build_eq {n N : Nat}
    (program : Vector Leanisa.instruction n)
    (covers : n ≤ N) (sizeBound : N ≤ 4294967296)
    (domain : GPowerDomain N)
    (nonzero : ∀ i : Fin N, gAddress i.val ≠ 0#64)
    (address : BitVec 64) :
    fetch_indexed program (build_address_index N) address =
      fetch program address := by
  have scanDomain := GPowerDomain.restrict domain covers
  cases hlookup : lookup_address (build_address_index N) address with
  | none =>
    have hnone := (build_index_lookup_none_iff N sizeBound domain nonzero address).mp hlookup
    have hmiss : ∀ i : Fin n, address ≠ gAddress i.val := by
      intro i
      exact hnone ⟨i.val, by omega⟩
    rw [fetch_indexed_lookup_none program (build_address_index N) address hlookup,
      fetch_miss program scanDomain address hmiss]
  | some offset =>
    obtain ⟨hltN, haddress⟩ :=
      (build_index_lookup_some_iff N sizeBound domain nonzero address offset).mp hlookup
    by_cases hlt : offset < n
    · rw [fetch_indexed_hit program (build_address_index N) address offset
        hlookup hlt, haddress]
      exact (fetch_gAddress program scanDomain ⟨offset, hlt⟩).symm
    · have hout : n ≤ offset := by omega
      have hmiss : ∀ i : Fin n, address ≠ gAddress i.val := by
        intro i
        rw [haddress]
        exact absent_shorter domain covers offset hltN hout i
      rw [fetch_indexed_out_of_range program (build_address_index N) address
        offset hlookup hout, fetch_miss program scanDomain address hmiss]

end Leanisa.Proofs.I1c1
