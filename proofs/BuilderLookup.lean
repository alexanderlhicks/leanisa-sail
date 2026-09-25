import CircularProbe

namespace Leanisa.Proofs.I1b
open Sail Leanisa.Functions Leanisa.Proofs.I1a

/-- The extracted lookup rejects the zero sentinel before probing. -/
theorem lookup_address_zero {n : Nat} (index : Vector address_entry n) :
    lookup_address index 0#64 = none := by
  simp [lookup_address, ExceptM.run]

/-- A missing probe result forces a missing lookup result. -/
theorem lookup_address_of_slot_none {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (hslot : address_slot index address = none) :
    lookup_address index address = none := by
  by_cases hz : address = 0#64
  · subst address
    exact lookup_address_zero index
  · simp [lookup_address, hz, hslot, ExceptM.run]

/-- With an actual in-bounds probe result, lookup checks the full key. -/
theorem lookup_address_of_slot_some {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (hz : address ≠ 0#64) (slot : Nat)
    (hslot : address_slot index address = some slot) :
    lookup_address index address =
      if (index[slot]!).address == address then some (index[slot]!).offset else none := by
  have hbound := address_slot_some_lt index address slot hslot
  simp [lookup_address, hz, hslot, hbound, ExceptM.run]
  by_cases heq : (index[slot]).address = address
  · simp [heq]
    rfl
  · simp [heq]
    rfl

theorem lookup_address_some_iff {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (offset : Nat) :
    lookup_address index address = some offset ↔
      address ≠ 0#64 ∧ ∃ slot : Nat,
        address_slot index address = some slot ∧
        (index[slot]!).address = address ∧
        (index[slot]!).offset = offset := by
  constructor
  · intro h
    have hz : address ≠ 0#64 := by
      intro heq
      subst address
      rw [lookup_address_zero] at h
      cases h
    constructor
    · exact hz
    · cases hslot : address_slot index address with
      | none =>
        rw [lookup_address_of_slot_none index address hslot] at h
        cases h
      | some slot =>
        rw [lookup_address_of_slot_some index address hz slot hslot] at h
        by_cases hkey : (index[slot]!).address = address
        · simp [hkey] at h
          exact ⟨slot, rfl, hkey, h⟩
        · simp [hkey] at h
  · rintro ⟨hz, slot, hslot, hkey, hoffset⟩
    rw [lookup_address_of_slot_some index address hz slot hslot]
    simp [hkey, hoffset]

end Leanisa.Proofs.I1b
