import IndexedScans

namespace Leanisa.Proofs.I1c1
open Sail Leanisa.Functions Leanisa.Proofs

/-- The generated memory reader alone falls back to the scan on a zero-cell
    index, regardless of the memory length. -/
theorem read_indexed_empty_fallback {n : Nat} (mem : Vector Word n)
    (index : Vector address_entry 0) (address : BitVec 64) :
    read_memory_indexed mem index address = read_memory mem address := by
  rfl

theorem read_indexed_hit {n capacity : Nat} (mem : Vector Word n)
    (index : Vector address_entry capacity) (hcapacity : 0 < capacity)
    (address : BitVec 64) (offset : Nat)
    (hlookup : lookup_address index address = some offset)
    (hoffset : offset < n) :
    read_memory_indexed mem index address =
      ⟨mem.get ⟨offset, hoffset⟩, true⟩ := by
  simp [read_memory_indexed, Vector.length, Nat.ne_of_gt hcapacity,
    hlookup, hoffset, ExceptM.run, Vector.get]

theorem read_indexed_out_of_range {n capacity : Nat} (mem : Vector Word n)
    (index : Vector address_entry capacity) (hcapacity : 0 < capacity)
    (address : BitVec 64) (offset : Nat)
    (hlookup : lookup_address index address = some offset)
    (hoffset : n ≤ offset) :
    read_memory_indexed mem index address = ⟨0#192, false⟩ := by
  have hnot : ¬ offset < n := by omega
  simp [read_memory_indexed, Vector.length, Nat.ne_of_gt hcapacity,
    hlookup, hnot, ExceptM.run]

theorem read_indexed_lookup_none {n capacity : Nat} (mem : Vector Word n)
    (index : Vector address_entry capacity) (hcapacity : 0 < capacity)
    (address : BitVec 64) (hlookup : lookup_address index address = none) :
    read_memory_indexed mem index address = ⟨0#192, false⟩ := by
  simp [read_memory_indexed, Vector.length, Nat.ne_of_gt hcapacity,
    hlookup, ExceptM.run]

theorem fetch_indexed_hit {n capacity : Nat}
    (program : Vector Leanisa.instruction n)
    (index : Vector address_entry capacity) (address : BitVec 64)
    (offset : Nat) (hlookup : lookup_address index address = some offset)
    (hoffset : offset < n) :
    fetch_indexed program index address = some (program.get ⟨offset, hoffset⟩) := by
  simp [fetch_indexed, Vector.length, hlookup, hoffset, ExceptM.run, Vector.get]

theorem fetch_indexed_out_of_range {n capacity : Nat}
    (program : Vector Leanisa.instruction n)
    (index : Vector address_entry capacity) (address : BitVec 64)
    (offset : Nat) (hlookup : lookup_address index address = some offset)
    (hoffset : n ≤ offset) :
    fetch_indexed program index address = none := by
  have hnot : ¬ offset < n := by omega
  simp [fetch_indexed, Vector.length, hlookup, hnot, ExceptM.run]

theorem fetch_indexed_lookup_none {n capacity : Nat}
    (program : Vector Leanisa.instruction n)
    (index : Vector address_entry capacity) (address : BitVec 64)
    (hlookup : lookup_address index address = none) :
    fetch_indexed program index address = none := by
  simp [fetch_indexed, hlookup, ExceptM.run]

end Leanisa.Proofs.I1c1
