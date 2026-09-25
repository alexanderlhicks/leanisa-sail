import IndexedSupported

namespace Leanisa.Proofs.I1c1.Checks
open Sail Leanisa Leanisa.Functions Leanisa.Proofs Leanisa.Proofs.I1c1

def oneMemory : Vector Word 1 := #v[7]
def twoMemory : Vector Word 2 := #v[7, 9]
def oneProgram : Vector instruction 1 := #v[.Set (1, 7)]
def twoProgram : Vector instruction 2 := #v[.Set (1, 7), .Set (2, 9)]

theorem zero_size_results :
    (read_memory_indexed (#v[] : Vector Word 0)
      (build_address_index 0) 1).value = 0#192 ∧
    (read_memory_indexed (#v[] : Vector Word 0)
      (build_address_index 0) 1).valid = false ∧
    (read_memory (#v[] : Vector Word 0) 1).valid = false ∧
    (fetch_indexed (#v[] : Vector instruction 0)
      (build_address_index 0) 1).isSome = false ∧
    (fetch (#v[] : Vector instruction 0) 1).isSome = false := by
  decide +kernel

theorem zero_size_exact (address : BitVec 64) :
    read_memory_indexed (#v[] : Vector Word 0)
      (build_address_index 0) address = ⟨0#192, false⟩ ∧
    read_memory (#v[] : Vector Word 0) address = ⟨0#192, false⟩ ∧
    fetch_indexed (#v[] : Vector instruction 0)
      (build_address_index 0) address = none ∧
    fetch (#v[] : Vector instruction 0) address = none := by
  have domain : GPowerDomain 0 := Supported.supported_domain 0 (by omega)
  have absent : ∀ i : Fin 0, address ≠ gAddress i.val := by
    intro i
    exact Fin.elim0 i
  have hread := read_memory_miss (#v[] : Vector Word 0) domain address absent
  have hfetch := fetch_miss (#v[] : Vector instruction 0) domain address absent
  have hindexedRead := supported_read_memory_indexed_build_eq (N := 0)
    (#v[] : Vector Word 0) (by omega) (by omega) address
  have hindexedFetch := supported_fetch_indexed_build_eq (N := 0)
    (#v[] : Vector instruction 0) (by omega) (by omega) address
  exact ⟨hindexedRead.trans hread, hread, hindexedFetch.trans hfetch, hfetch⟩

theorem singleton_results :
    (read_memory_indexed oneMemory (build_address_index 1) 1).value = 7 ∧
    (read_memory_indexed oneMemory (build_address_index 1) 1).valid = true ∧
    (fetch_indexed oneProgram (build_address_index 1) 1).isSome = true ∧
    (read_memory_indexed oneMemory (build_address_index 1) 0).valid = false ∧
    (fetch_indexed oneProgram (build_address_index 1) 2).isSome = false := by
  decide +kernel

theorem non_power_of_two_shorter_results :
    (read_memory_indexed twoMemory (build_address_index 3) 1).value = 7 ∧
    (read_memory_indexed twoMemory (build_address_index 3) 2).value = 9 ∧
    (fetch_indexed twoProgram (build_address_index 3) 2).isSome = true ∧
    lookup_address (build_address_index 3) 4 = some 2 ∧
    (read_memory_indexed twoMemory (build_address_index 3) 4).valid = false ∧
    (fetch_indexed twoProgram (build_address_index 3) 4).isSome = false ∧
    (read_memory_indexed twoMemory (build_address_index 3) 0).valid = false ∧
    (fetch_indexed twoProgram (build_address_index 3) 8).isSome = false := by
  decide +kernel

/-- A real builder hit outside the one-cell vector is rejected. -/
theorem shorter_vector_rejection :
    lookup_address (build_address_index 2) 2 = some 1 ∧
    (read_memory_indexed oneMemory (build_address_index 2) 2).valid = false ∧
    (read_memory oneMemory 2).valid = false ∧
    (fetch_indexed oneProgram (build_address_index 2) 2).isSome = false ∧
    (fetch oneProgram 2).isSome = false := by
  decide +kernel

theorem lookup_hit_does_not_bypass_vector_bound :
    ¬ (lookup_address (build_address_index 2) 2 = some 1 →
       (read_memory_indexed oneMemory (build_address_index 2) 2).valid = true) := by
  intro falseClaim
  have h := falseClaim shorter_vector_rejection.1
  rw [shorter_vector_rejection.2.1] at h
  cases h

/-- This genuine builder is deliberately too small for the two-cell vectors. -/
theorem uncovered_vectors_disagree :
    (read_memory_indexed twoMemory (build_address_index 1) 2).valid = false ∧
    (read_memory twoMemory 2).valid = true ∧
    (fetch_indexed twoProgram (build_address_index 1) 2).isSome = false ∧
    (fetch twoProgram 2).isSome = true := by
  decide +kernel

theorem coverage_cannot_be_dropped :
    ¬ (∀ mem : Vector Word 2,
      read_memory_indexed mem (build_address_index 1) 2 = read_memory mem 2) := by
  intro falseClaim
  have h := congrArg memory_read.valid (falseClaim twoMemory)
  rw [uncovered_vectors_disagree.1, uncovered_vectors_disagree.2.1] at h
  cases h

theorem fetch_coverage_cannot_be_dropped :
    ¬ (∀ program : Vector instruction 2,
      fetch_indexed program (build_address_index 1) 2 = fetch program 2) := by
  intro falseClaim
  have h := congrArg Option.isSome (falseClaim twoProgram)
  rw [uncovered_vectors_disagree.2.2.1,
    uncovered_vectors_disagree.2.2.2] at h
  cases h

def emptyTable : Vector address_entry 0 := #v[]

theorem empty_index_asymmetry :
    (read_memory_indexed oneMemory emptyTable 1).value = 7 ∧
    (read_memory_indexed oneMemory emptyTable 1).valid = true ∧
    (fetch_indexed oneProgram emptyTable 1).isSome = false ∧
    (fetch oneProgram 1).isSome = true := by
  decide +kernel

theorem empty_index_fetch_disagrees :
    fetch_indexed oneProgram emptyTable 1 ≠ fetch oneProgram 1 := by
  intro heq
  have h := congrArg Option.isSome heq
  rw [empty_index_asymmetry.2.2.1, empty_index_asymmetry.2.2.2] at h
  cases h

def wrongOffsetTable : Vector address_entry 2 :=
  #v[⟨1, 1⟩, ⟨1, 1⟩]

theorem forged_wrong_offset_values :
    (read_memory_indexed twoMemory wrongOffsetTable 1).valid = true ∧
    (read_memory twoMemory 1).valid = true ∧
    (read_memory_indexed twoMemory wrongOffsetTable 1).value = 9 ∧
    (read_memory twoMemory 1).value = 7 := by
  decide +kernel

theorem validity_alone_is_insufficient :
    ¬ (∀ index : Vector address_entry 2,
      (read_memory_indexed twoMemory index 1).valid =
        (read_memory twoMemory 1).valid →
      read_memory_indexed twoMemory index 1 = read_memory twoMemory 1) := by
  intro falseClaim
  have hvalid : (read_memory_indexed twoMemory wrongOffsetTable 1).valid =
      (read_memory twoMemory 1).valid := by
    rw [forged_wrong_offset_values.1, forged_wrong_offset_values.2.1]
  have heq := falseClaim wrongOffsetTable hvalid
  have hvalue := congrArg memory_read.value heq
  rw [forged_wrong_offset_values.2.2.1,
    forged_wrong_offset_values.2.2.2] at hvalue
  exact (by decide : (9#192) ≠ 7#192) hvalue

theorem maximal_source_capacity :
    2 * (2^32 : Nat) = 2^33 ∧
    (2^32 : Nat) - 1 ≤ 4294967295 ∧
    (2^33 : Nat) - 1 ≤ 8589934591 := by
  constructor
  · norm_num
  constructor <;> norm_num

end Leanisa.Proofs.I1c1.Checks
