import Leanisa

namespace Leanisa.Proofs.I1a
open Sail Leanisa.Functions

/-- The full 64-bit address mixer used by the extracted probe. -/
def mixedAddress (address : BitVec 64) : BitVec 64 :=
  (address ^^^ ((Sail.BitVec.extractLsb address 16 0) +++
    (Sail.BitVec.extractLsb address 63 17))) ^^^
  ((Sail.BitVec.extractLsb address 40 0) +++
    (Sail.BitVec.extractLsb address 63 41))

def startSlot (capacity : Nat) (address : BitVec 64) : Nat :=
  (mixedAddress address).toNat % capacity

/-- A slot qualifies when its full key is empty or equals the requested key. -/
def qualifies {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (position : Nat) : Bool :=
  ((index[position]!).address == 0#64) || ((index[position]!).address == address)

/-- Finite circular search, expressed as the least qualifying probe count. -/
def circularProbe {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) : Option Nat :=
  ((List.range n).find? fun t => (qualifies index address
    ((startSlot n address + t) % n))).map fun t =>
      (startSlot n address + t) % n

private def probeRange (n : Nat) : IntRange := { start := 0, stop := (n : Int) - 1 }

private def generatedBody {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (_probe : Int) (_h : _probe ∈ probeRange n) (slot : Nat) :
    ExceptM (Option Nat) (ForInStep Nat) := do
  let position := slot
  if ((position <b n) : Bool) then
    (do
      let entry := (GetElem?.getElem! index position)
      if (((entry.address == 0#64) || (entry.address == address)) : Bool)
      then throw ((some position) : Option Nat)
      else (pure ()))
  else (pure ())
  if (((position +i 1) <b n) : Bool)
  then (do
    let y ← (pure (position +i 1) : ExceptM (Option Nat) Int)
    pure PUnit.unit
    pure (.yield y.toNat))
  else (do
    let y ← (pure (0 : Int) : ExceptM (Option Nat) Int)
    pure PUnit.unit
    pure (.yield y.toNat))

private def generatedStart {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) : Nat :=
  let mixed :=
    ((address ^^^ ((Sail.BitVec.extractLsb address 16 0) +++
      (Sail.BitVec.extractLsb address 63 17))) ^^^
      ((Sail.BitVec.extractLsb address 40 0) +++
      (Sail.BitVec.extractLsb address 63 41)))
  let initial := Int.tmod (BitVec.toNatInt mixed) (Vector.length index)
  if ((initial <b (Vector.length index)) : Bool) then initial.toNat else 0

private theorem start_bridge (n : Nat) (address : BitVec 64) (hn : 0 < n) :
    (if Int.tmod (BitVec.toNatInt (mixedAddress address)) n <b (n : Int)
      then (Int.tmod (BitVec.toNatInt (mixedAddress address)) n).toNat
      else 0) = startSlot n address := by
  have hmod : Int.tmod (BitVec.toNatInt (mixedAddress address)) n =
    ((startSlot n address : Nat) : Int) := by
      simp only [Sail.BitVec.toNatInt, startSlot]
      exact (Int.ofNat_tmod (mixedAddress address).toNat n).symm
  rw [hmod]
  have hs : startSlot n address < n := Nat.mod_lt _ hn
  simp [hs]

private theorem next_mod (n x : Nat) (hn : 0 < n) :
    (if x % n + 1 < n then x % n + 1 else 0) = (x + 1) % n := by
  have hr : x % n < n := Nat.mod_lt _ hn
  have hm : (x + 1) % n = (x % n + 1) % n := by
    simp [Nat.add_mod]
  rw [hm]
  split
  · exact (Nat.mod_eq_of_lt ‹x % n + 1 < n›).symm
  · have heq : x % n + 1 = n := by omega
    simp [heq]

private theorem generated_unfold {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (hn : 0 < n) :
    address_slot index address = ExceptM.run (do
      let _ ← IntRange.forIn'.loop (m := ExceptM (Option Nat))
        (probeRange n) (generatedBody index address)
        (generatedStart index address) (0 : Int) (by simp [probeRange])
      pure (none : Option Nat)) := by
  unfold address_slot
  simp only [Vector.length, beq_iff_eq, Nat.ne_of_gt hn, ↓reduceIte]
  simp only [probeRange, ForIn.forIn, ForIn'.forIn', IntRange.forIn']
  simp only [generatedStart, Vector.length]
  unfold generatedBody
  simp only [bind_pure]
  rfl

private theorem generatedStart_eq {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (hn : 0 < n) :
    generatedStart index address = startSlot n address := by
  simpa only [generatedStart, Vector.length, mixedAddress] using start_bridge n address hn

private theorem generatedBody_bound {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (i : Int) (hi : i ∈ probeRange n)
    (slot : Nat) (hslot : slot < n) :
    generatedBody index address i hi slot =
      if qualifies index address slot then .error (some slot)
      else .ok (.yield (if slot + 1 < n then slot + 1 else 0)) := by
  by_cases hq : (index[slot]).address = 0#64 ∨ (index[slot]).address = address
  · simp [generatedBody, qualifies, hslot, hq]
    rfl
  · simp [generatedBody, qualifies, hslot, hq]
    have hlt : ((slot : Int) + 1 < n) ↔ slot + 1 < n := by omega
    simp [hlt]
    by_cases hnext : slot + 1 < n
    · simp [hnext]
      rfl
    · simp [hnext]
      rfl

private def nextSlot (n slot : Nat) : Nat := if slot + 1 < n then slot + 1 else 0

private theorem nextSlot_lt (n slot : Nat) (hn : 0 < n) : nextSlot n slot < n := by
  simp only [nextSlot]
  split
  · assumption
  · exact hn

private def searchM (p : Nat → Bool) (next : Nat → Nat) :
    Nat → Nat → ExceptM (Option Nat) Nat
  | 0, slot => .ok slot
  | k + 1, slot => if p slot then .error (some slot)
      else searchM p next k (next slot)

private theorem generated_loop_eq {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (hn : 0 < n) (j : Nat) (hj : j ≤ n)
    (slot : Nat) (hslot : slot < n)
    (hs : ((j : Int) - (probeRange n).start) % (probeRange n).step = 0) :
    IntRange.forIn'.loop (m := ExceptM (Option Nat)) (probeRange n)
      (generatedBody index address) slot j hs =
      searchM (qualifies index address) (nextSlot n) (n - j) slot := by
  rw [IntRange.forIn'.loop]
  by_cases hlt : j < n
  · have hin : (j : Int) ∈ probeRange n := by
      simp [probeRange, Membership.mem]
      omega
    simp only [dif_pos hin]
    have hsub : n - j = (n - (j + 1)) + 1 := by omega
    rw [hsub]
    rw [generatedBody_bound index address j hin slot hslot]
    by_cases hq : qualifies index address slot = true
    · simp [searchM, hq, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
      rfl
    · simp [searchM, hq, nextSlot, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
      exact generated_loop_eq index address hn (j + 1) (by omega)
        (nextSlot n slot) (nextSlot_lt n slot hn) _
  · have heq : j = n := by omega
    have hout : ¬ (j : Int) ∈ probeRange n := by
      simp [probeRange, Membership.mem]
      omega
    simp only [dif_neg hout]
    simp [heq, searchM]
    rfl
termination_by n - j

private def finish (r : ExceptM (Option Nat) Nat) : Option Nat :=
  match r with
  | .error result => result
  | .ok _ => none

private theorem run_eq_finish (r : ExceptM (Option Nat) Nat) :
    ExceptM.run (do let _ ← r; pure (none : Option Nat)) = finish r := by
  cases r <;> rfl

private theorem finish_searchM_tail {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (hn : 0 < n) (j : Nat) (hj : j ≤ n) :
    finish (searchM (qualifies index address) (nextSlot n) (n - j)
      ((startSlot n address + j) % n)) =
    ((List.range' j (n - j)).find? fun t => qualifies index address
      ((startSlot n address + t) % n)).map fun t =>
        (startSlot n address + t) % n := by
  induction h : n - j using Nat.strongRecOn generalizing j with
  | ind k ih =>
    subst k
    by_cases hzero : j = n
    · subst j
      simp [finish, searchM]
    · have hlt : j < n := by omega
      have hsub : n - j = (n - (j + 1)) + 1 := by omega
      rw [hsub]
      rw [List.range'_succ]
      simp only [List.find?_cons, Option.map]
      by_cases hq : qualifies index address ((startSlot n address + j) % n) = true
      · simp [searchM, finish, hq]
      · simp [searchM, finish, hq]
        have hnext : nextSlot n ((startSlot n address + j) % n) =
            (startSlot n address + (j + 1)) % n := by
          simpa [nextSlot, Nat.add_assoc] using
            next_mod n (startSlot n address + j) hn
        rw [hnext]
        exact ih (n - (j + 1)) (by omega) (j + 1) (by omega) rfl

/-- The extracted Sail operation equals the structural finite search for every table. -/
theorem address_slot_eq_circularProbe {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) :
    address_slot index address = circularProbe index address := by
  by_cases hn : 0 < n
  · rw [generated_unfold index address hn]
    have hs : generatedStart index address < n := by
      rw [generatedStart_eq index address hn]
      exact Nat.mod_lt _ hn
    have hloop := generated_loop_eq index address hn 0 (by omega)
      (generatedStart index address) hs (by simp [probeRange])
    simp only [Nat.sub_zero] at hloop
    calc
      _ = ExceptM.run (do
          let _ ← searchM (qualifies index address) (nextSlot n) n
            (generatedStart index address)
          pure (none : Option Nat)) :=
        congrArg (fun r : ExceptM (Option Nat) Nat => ExceptM.run (do
          let _ ← r
          pure (none : Option Nat))) hloop
      _ = circularProbe index address := by
        rw [generatedStart_eq index address hn]
        rw [run_eq_finish]
        have hstartmod : startSlot n address % n = startSlot n address :=
          Nat.mod_eq_of_lt (Nat.mod_lt _ hn)
        have htail := finish_searchM_tail index address hn 0 (by omega)
        simp only [Nat.sub_zero, Nat.add_zero, hstartmod] at htail
        simpa [circularProbe, List.range_eq_range'] using
          htail
  · have hzero : n = 0 := by omega
    subst n
    simp [address_slot, circularProbe, ExceptM.run]

/-- A returned slot is exactly the first qualifying position in the cycle. -/
theorem address_slot_some_iff {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (slot : Nat) :
    address_slot index address = some slot ↔
      ∃ t : Nat, t < n ∧ slot = (startSlot n address + t) % n ∧
        qualifies index address ((startSlot n address + t) % n) = true ∧
        ∀ u : Nat, u < t →
          qualifies index address ((startSlot n address + u) % n) = false := by
  rw [address_slot_eq_circularProbe]
  unfold circularProbe
  constructor
  · intro h
    cases hf : (List.range n).find? (fun t => qualifies index address
        ((startSlot n address + t) % n)) with
    | none => simp [hf] at h
    | some t =>
      have hfind := (List.find?_range_eq_some.mp hf)
      simp only [hf, Option.map_some, Option.some.injEq] at h
      refine ⟨t, ?_, h.symm, ?_, ?_⟩
      · simpa using hfind.2.1
      · exact hfind.1
      · intro u hu
        have hno := hfind.2.2 u hu
        simpa using hno
  · rintro ⟨t, ht, hslot, hqual, hearlier⟩
    have hf : (List.range n).find? (fun u => qualifies index address
        ((startSlot n address + u) % n)) = some t := by
      apply List.find?_range_eq_some.mpr
      refine ⟨hqual, ?_, ?_⟩
      · simpa using ht
      · intro u hu
        simp [hearlier u hu]
    simp only [hf, Option.map_some, Option.some.injEq]
    exact hslot.symm

/-- `none` means that no position in the complete cycle qualifies. -/
theorem address_slot_none_iff {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) :
    address_slot index address = none ↔
      ∀ t : Nat, t < n →
        qualifies index address ((startSlot n address + t) % n) = false := by
  rw [address_slot_eq_circularProbe]
  unfold circularProbe
  rw [Option.map_eq_none_iff]
  rw [List.find?_range_eq_none]
  constructor
  · intro h t ht
    simpa using h t ht
  · intro h t ht
    simpa using h t ht

theorem address_slot_some_lt {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (slot : Nat)
    (h : address_slot index address = some slot) : slot < n := by
  obtain ⟨t, ht, hslot, _, _⟩ := (address_slot_some_iff index address slot).mp h
  rw [hslot]
  exact Nat.mod_lt _ (by omega)

private theorem modular_start_injective (n start t u : Nat) (hs : start < n)
    (ht : t < n) (hu : u < n)
    (he : (start + t) % n = (start + u) % n) : t = u := by
  by_cases hst : start + t < n
  · by_cases hsu : start + u < n
    · rw [Nat.mod_eq_of_lt hst, Nat.mod_eq_of_lt hsu] at he
      omega
    · have hsu' : n ≤ start + u := by omega
      have hsum : start + u - n < n := by omega
      rw [Nat.mod_eq_of_lt hst, Nat.mod_eq_sub_mod hsu', Nat.mod_eq_of_lt hsum] at he
      omega
  · have hst' : n ≤ start + t := by omega
    have hsumt : start + t - n < n := by omega
    by_cases hsu : start + u < n
    · rw [Nat.mod_eq_sub_mod hst', Nat.mod_eq_of_lt hsumt,
        Nat.mod_eq_of_lt hsu] at he
      omega
    · have hsu' : n ≤ start + u := by omega
      have hsumu : start + u - n < n := by omega
      rw [Nat.mod_eq_sub_mod hst', Nat.mod_eq_of_lt hsumt,
        Nat.mod_eq_sub_mod hsu', Nat.mod_eq_of_lt hsumu] at he
      omega

private theorem modular_start_surjective (n start slot : Nat)
    (hs : start < n) (hslot : slot < n) :
    ∃ t : Nat, t < n ∧ (start + t) % n = slot := by
  by_cases h : slot < start
  · refine ⟨slot + n - start, by omega, ?_⟩
    have he : start + (slot + n - start) = slot + n := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hslot]
  · refine ⟨slot - start, by omega, ?_⟩
    have he : start + (slot - start) = slot := by omega
    rw [he, Nat.mod_eq_of_lt hslot]

/-- The first `n` circular positions enumerate every `Fin n` once. -/
theorem probe_positions_bijective (n : Nat) (hn : 0 < n)
    (address : BitVec 64) :
    Function.Injective (fun t : Fin n =>
      (⟨(startSlot n address + t.val) % n, Nat.mod_lt _ hn⟩ : Fin n)) ∧
    Function.Surjective (fun t : Fin n =>
      (⟨(startSlot n address + t.val) % n, Nat.mod_lt _ hn⟩ : Fin n)) := by
  have hs : startSlot n address < n := Nat.mod_lt _ hn
  constructor
  · intro t u h
    apply Fin.ext
    apply modular_start_injective n (startSlot n address) t.val u.val
      hs t.isLt u.isLt
    exact congrArg Fin.val h
  · intro slot
    obtain ⟨t, ht, hpos⟩ := modular_start_surjective n
      (startSlot n address) slot.val hs slot.isLt
    exact ⟨⟨t, ht⟩, Fin.ext hpos⟩

theorem address_slot_exists_of_qualifying {n : Nat} (index : Vector address_entry n)
    (address : BitVec 64) (hn : 0 < n) (slot : Fin n)
    (hq : qualifies index address slot.val = true) :
    ∃ result : Nat, address_slot index address = some result := by
  obtain ⟨t, ht⟩ := (probe_positions_bijective n hn address).2 slot
  by_cases hnone : address_slot index address = none
  · have hall := (address_slot_none_iff index address).mp hnone
    have hfalse := hall t.val t.isLt
    have hsame : (startSlot n address + t.val) % n = slot.val :=
      congrArg Fin.val ht
    rw [hsame] at hfalse
    simp [hq] at hfalse
  · cases h : address_slot index address with
    | none => exact False.elim (hnone h)
    | some result => exact ⟨result, rfl⟩

/-- The Sail signature admits capacities at most `2^33`. -/
theorem address_slot_sail_domain {n : Nat} (_hcap : n ≤ 8589934592)
    (index : Vector address_entry n) (address : BitVec 64) :
    address_slot index address = circularProbe index address ∧
    ∀ slot : Nat, address_slot index address = some slot → slot < n := by
  exact ⟨address_slot_eq_circularProbe index address,
    fun slot h => address_slot_some_lt index address slot h⟩

end Leanisa.Proofs.I1a
