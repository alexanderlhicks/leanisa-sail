import BuilderPlacement
import BuilderLookup

namespace Leanisa.Proofs.I1b
open Sail Leanisa.Functions Leanisa.Proofs Leanisa.Proofs.I1a

theorem placement_probe_hit {size : Nat}
    (domain : GPowerDomain size)
    {table : Vector address_entry (2 * size)}
    (placement : Placement size size table)
    (i : Fin size) :
    address_slot table (gAddress i.val) = some (placement.loc i).val := by
  have hcap : 0 < 2 * size := by have := i.isLt; omega
  obtain ⟨t, ht, hposition, hearlier⟩ := placement.earlier_nonzero i
  apply (address_slot_some_iff table (gAddress i.val) (placement.loc i).val).mpr
  refine ⟨t, ht, hposition.symm, ?_, ?_⟩
  · have hkey : (table[(placement.loc i).val]!).address = gAddress i.val := by
      have hget : table[(placement.loc i).val]! = table.get (placement.loc i) :=
        getElem!_pos table (placement.loc i).val (placement.loc i).isLt
      rw [hget, placement.placed i]
    simp only [qualifies, hposition, Bool.or_eq_true, beq_iff_eq]
    right
    simpa only [getElem!_pos table (placement.loc i).val (placement.loc i).isLt]
      using hkey
  · intro u hu
    have hnon := hearlier u hu
    have hpos : (startSlot (2 * size) (gAddress i.val) + u) %
        (2 * size) < 2 * size := Nat.mod_lt _ hcap
    have hnotkey : (table[(startSlot (2 * size) (gAddress i.val) + u) %
        (2 * size)]!).address ≠ gAddress i.val := by
      intro hkey
      have hentry : table[(startSlot (2 * size) (gAddress i.val) + u) %
          (2 * size)]! = table.get ⟨_, hpos⟩ :=
        getElem!_pos table _ hpos
      have hoccupied : (table.get ⟨_, hpos⟩).address ≠ 0#64 := by
        simpa [hentry] using hnon
      obtain ⟨j, hj⟩ := occupied_has_index placement ⟨_, hpos⟩ hoccupied
      have htablekey : (table.get ⟨_, hpos⟩).address = gAddress i.val := by
        simpa [hentry] using hkey
      rw [← hj, placement.placed j] at htablekey
      have hji : j = i := domain.distinct j i htablekey
      have hposEq : (startSlot (2 * size) (gAddress i.val) + u) %
          (2 * size) = (placement.loc i).val := by
        have hjVal := congrArg Fin.val hj
        rw [hji] at hjVal
        exact hjVal.symm
      have hmod : (startSlot (2 * size) (gAddress i.val) + u) %
          (2 * size) = (startSlot (2 * size) (gAddress i.val) + t) %
          (2 * size) := by rw [hposition]; exact hposEq
      have huFin : u < 2 * size := by omega
      have htime : (⟨u, huFin⟩ : Fin (2 * size)) = ⟨t, ht⟩ :=
        (probe_positions_bijective (2 * size) hcap (gAddress i.val)).1
          (Fin.ext hmod)
      have heq := congrArg Fin.val htime
      simp only at heq
      omega
    simp [qualifies, hnon, hnotkey]

theorem placement_lookup_hit {size : Nat}
    (domain : GPowerDomain size)
    (nonzero : ∀ i : Fin size, gAddress i.val ≠ 0#64)
    {table : Vector address_entry (2 * size)}
    (placement : Placement size size table)
    (i : Fin size) :
    lookup_address table (gAddress i.val) = some i.val := by
  have hslot := placement_probe_hit domain placement i
  rw [lookup_address_of_slot_some table (gAddress i.val) (nonzero i)
    (placement.loc i).val hslot]
  have hget : table[(placement.loc i).val]! = table.get (placement.loc i) :=
    getElem!_pos table (placement.loc i).val (placement.loc i).isLt
  rw [hget, placement.placed i]
  simp

/-- An actual lookup succeeds exactly for an address in the placed domain. -/
theorem placement_lookup_some_iff {size : Nat}
    (domain : GPowerDomain size)
    (nonzero : ∀ i : Fin size, gAddress i.val ≠ 0#64)
    {table : Vector address_entry (2 * size)}
    (placement : Placement size size table)
    (address : BitVec 64) (offset : Nat) :
    lookup_address table address = some offset ↔
      offset < size ∧ address = gAddress offset := by
  constructor
  · intro h
    obtain ⟨hz, slot, hslot, hkey, hoffset⟩ :=
      (lookup_address_some_iff table address offset).mp h
    have hbound := address_slot_some_lt table address slot hslot
    have hentry : table[slot]! = table.get ⟨slot, hbound⟩ :=
      getElem!_pos table slot hbound
    have hoccupied : (table.get ⟨slot, hbound⟩).address ≠ 0#64 := by
      rw [←hentry, hkey]
      exact hz
    obtain ⟨i, hi⟩ := occupied_has_index placement ⟨slot, hbound⟩ hoccupied
    rw [hentry, ←hi, placement.placed i] at hkey hoffset
    have hval : i.val = offset := by simpa using hoffset
    have haddr : gAddress i.val = address := by simpa using hkey
    constructor
    · have := i.isLt
      omega
    · simpa [←hval] using haddr.symm
  · rintro ⟨hoffset, haddress⟩
    rw [haddress]
    exact placement_lookup_hit domain nonzero placement ⟨offset, hoffset⟩

theorem placement_lookup_none_iff {size : Nat}
    (domain : GPowerDomain size)
    (nonzero : ∀ i : Fin size, gAddress i.val ≠ 0#64)
    {table : Vector address_entry (2 * size)}
    (placement : Placement size size table)
    (address : BitVec 64) :
    lookup_address table address = none ↔
      ∀ i : Fin size, address ≠ gAddress i.val := by
  constructor
  · intro h i heq
    have hhit := placement_lookup_hit domain nonzero placement i
    rw [←heq, h] at hhit
    cases hhit
  · intro h
    cases hlookup : lookup_address table address with
    | none => rfl
    | some offset =>
      obtain ⟨hoffset, heq⟩ :=
        (placement_lookup_some_iff domain nonzero placement address offset).mp hlookup
      exact False.elim ((h ⟨offset, hoffset⟩) heq)

/-- Correctness of the generated builder and generated lookup, under explicit
    finite-domain and nonzero premises. -/
theorem build_index_lookup_some_iff (size : Nat)
    (sizeBound : size ≤ 4294967296)
    (domain : GPowerDomain size)
    (nonzero : ∀ i : Fin size, gAddress i.val ≠ 0#64)
    (address : BitVec 64) (offset : Nat) :
    lookup_address (build_address_index size) address = some offset ↔
      offset < size ∧ address = gAddress offset := by
  obtain ⟨placement⟩ := build_index_placement size sizeBound domain nonzero
  exact placement_lookup_some_iff domain nonzero placement address offset

theorem build_index_lookup_none_iff (size : Nat)
    (sizeBound : size ≤ 4294967296)
    (domain : GPowerDomain size)
    (nonzero : ∀ i : Fin size, gAddress i.val ≠ 0#64)
    (address : BitVec 64) :
    lookup_address (build_address_index size) address = none ↔
      ∀ i : Fin size, address ≠ gAddress i.val := by
  obtain ⟨placement⟩ := build_index_placement size sizeBound domain nonzero
  exact placement_lookup_none_iff domain nonzero placement address

theorem build_index_probe_slot_bound (size : Nat)
    (sizeBound : size ≤ 4294967296)
    (address : BitVec 64) (slot : Nat)
    (hslot : address_slot (build_address_index size) address = some slot) :
    slot ≤ 8589934591 :=
  source_slot_bound sizeBound
    (address_slot_some_lt (build_address_index size) address slot hslot)

theorem build_index_lookup_offset_bound (size : Nat)
    (sizeBound : size ≤ 4294967296)
    (domain : GPowerDomain size)
    (nonzero : ∀ i : Fin size, gAddress i.val ≠ 0#64)
    (address : BitVec 64) (offset : Nat)
    (hlookup : lookup_address (build_address_index size) address = some offset) :
    offset ≤ 4294967295 := by
  have hoffset := (build_index_lookup_some_iff size sizeBound domain nonzero
    address offset).mp hlookup |>.1
  exact source_offset_bound sizeBound hoffset

end Leanisa.Proofs.I1b
