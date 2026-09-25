import BuilderLoop
import Lookup
import Mathlib.Data.Fintype.Card

namespace Leanisa.Proofs.I1b
open Sail Leanisa.Functions Leanisa.Proofs Leanisa.Proofs.I1a

/-- A finite prefix's exact occupied entries, blank complement, and probe paths. -/
structure Placement (size k : Nat) (table : Vector address_entry (2 * size)) where
  loc : Fin k → Fin (2 * size)
  injective : Function.Injective loc
  placed : ∀ i : Fin k,
    table.get (loc i) = ⟨gAddress i.val, i.val⟩
  blank : ∀ slot : Fin (2 * size),
    (∀ i : Fin k, loc i ≠ slot) → table.get slot = emptyEntry
  earlier_nonzero : ∀ i : Fin k,
    ∃ t : Nat, t < 2 * size ∧
      (startSlot (2 * size) (gAddress i.val) + t) % (2 * size) = (loc i).val ∧
      ∀ u : Nat, u < t →
        (table[(startSlot (2 * size) (gAddress i.val) + u) % (2 * size)]!).address ≠ 0#64

def initial_placement (size : Nat) :
    Placement size 0 (initialState size).2 := by
  refine ⟨(fun i => Fin.elim0 i), ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro slot _
    simp [initialState, emptyEntry, vectorInit, Vector.get]
  · intro i
    exact Fin.elim0 i

def StateInvariant (size k : Nat)
    (state : BitVec 64 × Vector address_entry (2 * size)) : Prop :=
  Nonempty (Placement size k state.2) ∧
    (k < size → state.1 = gAddress k)

theorem initial_state_invariant (size : Nat) (domain : GPowerDomain size) :
    StateInvariant size 0 (initialState size) := by
  constructor
  · exact ⟨initial_placement size⟩
  · intro h
    simpa [initialState] using domain.origin.symm

theorem free_slot {size k : Nat} (hk : k < size)
    {table : Vector address_entry (2 * size)}
    (placement : Placement size k table) :
    ∃ slot : Fin (2 * size), ∀ i : Fin k, placement.loc i ≠ slot := by
  have hcap : k < 2 * size := by omega
  by_contra h
  push Not at h
  have hsurj : Function.Surjective placement.loc := by
    intro slot
    obtain ⟨i, hi⟩ := h slot
    exact ⟨i, hi⟩
  have hcard := Fintype.card_le_of_surjective placement.loc hsurj
  simp only [Fintype.card_fin] at hcard
  omega

theorem placed_nonzero {size k : Nat} (hk : k ≤ size)
    {table : Vector address_entry (2 * size)}
    (placement : Placement size k table)
    (nonzero : ∀ i : Fin size, gAddress i.val ≠ 0#64)
    (i : Fin k) : (table.get (placement.loc i)).address ≠ 0#64 := by
  rw [placement.placed i]
  exact nonzero ⟨i.val, by omega⟩

theorem occupied_has_index {size k : Nat}
    {table : Vector address_entry (2 * size)}
    (placement : Placement size k table)
    (slot : Fin (2 * size))
    (hoccupied : (table.get slot).address ≠ 0#64) :
    ∃ i : Fin k, placement.loc i = slot := by
  by_contra h
  push Not at h
  have hempty := placement.blank slot h
  rw [hempty] at hoccupied
  exact hoccupied rfl

theorem fresh_key_not_placed {size k : Nat} (hk : k < size)
    (domain : GPowerDomain size)
    {table : Vector address_entry (2 * size)}
    (placement : Placement size k table) (i : Fin k) :
    (table.get (placement.loc i)).address ≠ gAddress k := by
  rw [placement.placed i]
  intro heq
  have hsame := domain.distinct
    ⟨i.val, by omega⟩ ⟨k, hk⟩ heq
  have hval := congrArg Fin.val hsame
  simp at hval
  omega

theorem fresh_qualifies_iff_empty {size k : Nat} (hk : k < size)
    (domain : GPowerDomain size)
    {table : Vector address_entry (2 * size)}
    (placement : Placement size k table) (slot : Nat)
    (hslot : slot < 2 * size) :
    qualifies table (gAddress k) slot = true ↔
      (table[slot]!).address = 0#64 := by
  have hentry : table[slot]! = table.get ⟨slot, hslot⟩ := by
    simpa [Vector.get] using (getElem!_pos table slot hslot)
  constructor
  · intro hq
    simp only [qualifies, Bool.or_eq_true, beq_iff_eq] at hq
    rcases hq with hzero | hkey
    · exact hzero
    · by_contra hnonzero
      have hoccupied : (table.get ⟨slot, hslot⟩).address ≠ 0#64 := by
        simpa [hentry] using hnonzero
      obtain ⟨i, hi⟩ := occupied_has_index placement ⟨slot, hslot⟩ hoccupied
      have hne := fresh_key_not_placed hk domain placement i
      rw [hi] at hne
      exact hne (by simpa [hentry] using hkey)
  · intro hzero
    simp [qualifies, hzero]

theorem insertion_slot {size k : Nat} (hk : k < size)
    (domain : GPowerDomain size)
    {table : Vector address_entry (2 * size)}
    (placement : Placement size k table) :
    ∃ slot : Nat,
      address_slot table (gAddress k) = some slot ∧
      slot < 2 * size ∧ (table[slot]!).address = 0#64 ∧
      ∃ t : Nat, t < 2 * size ∧
        (startSlot (2 * size) (gAddress k) + t) % (2 * size) = slot ∧
        ∀ u : Nat, u < t →
          (table[(startSlot (2 * size) (gAddress k) + u) % (2 * size)]!).address ≠ 0#64 := by
  have hcap : 0 < 2 * size := by omega
  obtain ⟨free, hfree⟩ := free_slot hk placement
  have hblank := placement.blank free hfree
  have hq : qualifies table (gAddress k) free.val = true := by
    have hentry : table[free.val]! = table.get free :=
      getElem!_pos table free.val free.isLt
    have hzero : (table[free.val]!).address = 0#64 := by
      rw [hentry, hblank]
      rfl
    simp only [qualifies, hzero, beq_self_eq_true, Bool.true_or]
  obtain ⟨slot, hprobe⟩ := address_slot_exists_of_qualifying table
    (gAddress k) hcap free hq
  have hbound := address_slot_some_lt table (gAddress k) slot hprobe
  obtain ⟨t, ht, hposition, hhit, hearlier⟩ :=
    (address_slot_some_iff table (gAddress k) slot).mp hprobe
  have hzero : (table[slot]!).address = 0#64 := by
    apply (fresh_qualifies_iff_empty hk domain placement slot hbound).mp
    simpa [hposition] using hhit
  refine ⟨slot, hprobe, hbound, hzero, t, ht, hposition.symm, ?_⟩
  intro u hu
  have hmiss := hearlier u hu
  intro hzeroEarlier
  have hqual : qualifies table (gAddress k)
      ((startSlot (2 * size) (gAddress k) + u) % (2 * size)) = true := by
    simp [qualifies, hzeroEarlier]
  rw [hqual] at hmiss
  cases hmiss

def extendLoc {size k : Nat} (loc : Fin k → Fin (2 * size))
    (newSlot : Fin (2 * size)) (i : Fin (k + 1)) : Fin (2 * size) :=
  if h : i.val < k then loc ⟨i.val, h⟩ else newSlot

theorem extendLoc_old {size k : Nat} (loc : Fin k → Fin (2 * size))
    (newSlot : Fin (2 * size)) (i : Fin k) :
    extendLoc loc newSlot i.castSucc = loc i := by
  simp [extendLoc, i.isLt]

theorem extendLoc_last {size k : Nat} (loc : Fin k → Fin (2 * size))
    (newSlot : Fin (2 * size)) :
    extendLoc loc newSlot (Fin.last k) = newSlot := by
  simp [extendLoc]

theorem extendLoc_injective {size k : Nat}
    (loc : Fin k → Fin (2 * size)) (hinj : Function.Injective loc)
    (newSlot : Fin (2 * size)) (hfresh : ∀ i : Fin k, loc i ≠ newSlot) :
    Function.Injective (extendLoc loc newSlot) := by
  intro i j hij
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [extendLoc, dif_pos hi, dif_pos hj] at hij
      have hsame := hinj hij
      apply Fin.ext
      exact congrArg (fun x : Fin k => x.val) hsame
    · simp only [extendLoc, dif_pos hi, dif_neg hj] at hij
      exact False.elim ((hfresh ⟨i.val, hi⟩) hij)
  · by_cases hj : j.val < k
    · simp only [extendLoc, dif_neg hi, dif_pos hj] at hij
      exact False.elim ((hfresh ⟨j.val, hj⟩) hij.symm)
    · apply Fin.ext
      have hiEq : i.val = k := by omega
      have hjEq : j.val = k := by omega
      omega

theorem vectorUpdate_get {n : Nat} (table : Vector address_entry n)
    (slot : Nat) (_hslot : slot < n) (entry : address_entry) (pos : Fin n) :
    (vectorUpdate table slot entry).get pos =
      if slot = pos.val then entry else table.get pos := by
  change (table.set! slot entry)[pos.val] =
    if slot = pos.val then entry else table[pos.val]
  rw [show table.set! slot entry = table.setIfInBounds slot entry by rfl]
  exact Vector.getElem_setIfInBounds pos.isLt

theorem vectorUpdate_preserves_nonzero {n : Nat}
    (table : Vector address_entry n) (slot : Nat) (hslot : slot < n)
    (entry : address_entry) (hentry : entry.address ≠ 0#64)
    (pos : Nat) (hpos : pos < n)
    (hold : (table[pos]!).address ≠ 0#64) :
    ((vectorUpdate table slot entry)[pos]!).address ≠ 0#64 := by
  have hget := vectorUpdate_get table slot hslot entry ⟨pos, hpos⟩
  have hleft : (vectorUpdate table slot entry)[pos]! =
      (vectorUpdate table slot entry).get ⟨pos, hpos⟩ :=
    getElem!_pos _ pos hpos
  have hright : table[pos]! = table.get ⟨pos, hpos⟩ :=
    getElem!_pos _ pos hpos
  rw [hleft, hget]
  by_cases heq : slot = pos
  · simp [heq, hentry]
  · simp only [if_neg heq]
    simpa [hright] using hold

def insertedEntry (k : Nat) : address_entry := ⟨gAddress k, k⟩

def extend_placement {size k : Nat} (hk : k < size)
    (nonzero : ∀ i : Fin size, gAddress i.val ≠ 0#64)
    {table : Vector address_entry (2 * size)}
    (placement : Placement size k table)
    (slot : Nat) (hslot : slot < 2 * size)
    (hzero : (table[slot]!).address = 0#64)
    (hpath : ∃ t : Nat, t < 2 * size ∧
      (startSlot (2 * size) (gAddress k) + t) % (2 * size) = slot ∧
      ∀ u : Nat, u < t →
        (table[(startSlot (2 * size) (gAddress k) + u) % (2 * size)]!).address ≠ 0#64) :
    Placement size (k + 1) (vectorUpdate table slot (insertedEntry k)) := by
  let newSlot : Fin (2 * size) := ⟨slot, hslot⟩
  have hentry : table[slot]! = table.get newSlot :=
    getElem!_pos _ slot hslot
  have hfresh : ∀ i : Fin k, placement.loc i ≠ newSlot := by
    intro i heq
    have hnon := placed_nonzero (Nat.le_of_lt hk) placement nonzero i
    rw [heq] at hnon
    exact hnon (by simpa [hentry] using hzero)
  have hnewnonzero : (insertedEntry k).address ≠ 0#64 :=
    nonzero ⟨k, hk⟩
  refine ⟨extendLoc placement.loc newSlot,
    extendLoc_injective placement.loc placement.injective newSlot hfresh,
    ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < k
    · let i : Fin k := ⟨j.val, hj⟩
      have hloc : extendLoc placement.loc newSlot j = placement.loc i := by
        simp [extendLoc, hj, i]
      rw [hloc, vectorUpdate_get table slot hslot (insertedEntry k) (placement.loc i)]
      have hne : slot ≠ (placement.loc i).val := by
        intro heq
        exact hfresh i (Fin.ext heq.symm)
      simp only [if_neg hne]
      simpa [i] using placement.placed i
    · have hjlast : j.val = k := by omega
      have hloc : extendLoc placement.loc newSlot j = newSlot := by
        simp [extendLoc, hj]
      rw [hloc, vectorUpdate_get table slot hslot (insertedEntry k) newSlot]
      simp [newSlot, insertedEntry, hjlast]
  · intro q houtside
    have hne : slot ≠ q.val := by
      intro heq
      have hsame : newSlot = q := Fin.ext heq
      exact houtside (Fin.last k) (by rw [extendLoc_last]; exact hsame)
    have holdoutside : ∀ i : Fin k, placement.loc i ≠ q := by
      intro i heq
      exact houtside i.castSucc (by rw [extendLoc_old]; exact heq)
    have hblank := placement.blank q holdoutside
    rw [vectorUpdate_get table slot hslot (insertedEntry k) q]
    simp [hne, hblank]
  · intro j
    have hcap : 0 < 2 * size := by omega
    by_cases hj : j.val < k
    · let i : Fin k := ⟨j.val, hj⟩
      obtain ⟨t, ht, hposition, hearlier⟩ := placement.earlier_nonzero i
      refine ⟨t, ht, ?_, ?_⟩
      · simpa [extendLoc, hj, i] using hposition
      · intro u hu
        have hpos : (startSlot (2 * size) (gAddress j.val) + u) %
            (2 * size) < 2 * size := Nat.mod_lt _ hcap
        exact vectorUpdate_preserves_nonzero table slot hslot
          (insertedEntry k) hnewnonzero _ hpos (hearlier u hu)
    · have hjlast : j.val = k := by omega
      obtain ⟨t, ht, hposition, hearlier⟩ := hpath
      refine ⟨t, ht, ?_, ?_⟩
      · simpa [extendLoc, hj, hjlast, newSlot] using hposition
      · intro u hu
        have hpos : (startSlot (2 * size) (gAddress j.val) + u) %
            (2 * size) < 2 * size := Nat.mod_lt _ hcap
        have hold : (table[(startSlot (2 * size) (gAddress j.val) + u) %
            (2 * size)]!).address ≠ 0#64 := by
          simpa [hjlast] using hearlier u hu
        exact vectorUpdate_preserves_nonzero table slot hslot
          (insertedEntry k) hnewnonzero _ hpos hold

theorem builderStep_at_slot {size k : Nat}
    (state : BitVec 64 × Vector address_entry (2 * size))
    (haddress : state.1 = gAddress k)
    (slot : Nat) (hprobe : address_slot state.2 (gAddress k) = some slot)
    (hslot : slot < 2 * size) :
    builderStep size k state =
      (advance (gAddress k), vectorUpdate state.2 slot (insertedEntry k)) := by
  simp [builderStep, haddress, hprobe, hslot, insertedEntry]

/-- At every valid prefix, the extracted builder's silent `none` and
    out-of-range branches are unreachable. -/
theorem builderStep_progress {size k : Nat} (hk : k < size)
    (domain : GPowerDomain size)
    (state : BitVec 64 × Vector address_entry (2 * size))
    (haddress : state.1 = gAddress k)
    (placement : Placement size k state.2) :
    ∃ slot : Nat,
      address_slot state.2 (gAddress k) = some slot ∧
      slot < 2 * size ∧
      builderStep size k state =
        (advance (gAddress k), vectorUpdate state.2 slot (insertedEntry k)) := by
  obtain ⟨slot, hprobe, hslot, _, _⟩ := insertion_slot hk domain placement
  exact ⟨slot, hprobe, hslot,
    builderStep_at_slot state haddress slot hprobe hslot⟩

theorem state_invariant_step {size k : Nat} (hk : k < size)
    (domain : GPowerDomain size)
    (nonzero : ∀ i : Fin size, gAddress i.val ≠ 0#64)
    (state : BitVec 64 × Vector address_entry (2 * size))
    (hinv : StateInvariant size k state) :
    StateInvariant size (k + 1) (builderStep size k state) := by
  obtain ⟨⟨placement⟩, haddressInv⟩ := hinv
  have haddress := haddressInv hk
  obtain ⟨slot, hprobe, hslot, hzero, hpath⟩ :=
    insertion_slot hk domain placement
  have hstep := builderStep_at_slot state haddress slot hprobe hslot
  rw [hstep]
  constructor
  · exact ⟨extend_placement hk nonzero placement slot hslot hzero hpath⟩
  · intro hnext
    exact (domain.successor k hnext).symm

/-- The actual extracted builder produces a complete placement map. -/
theorem build_index_placement (size : Nat) (_sizeBound : size ≤ 4294967296)
    (domain : GPowerDomain size)
    (nonzero : ∀ i : Fin size, gAddress i.val ≠ 0#64) :
    Nonempty (Placement size size (build_address_index size)) := by
  have hinit := initial_state_invariant size domain
  have hfinal := builderSteps_invariant size (StateInvariant size)
    (fun k hk state hinv => state_invariant_step hk domain nonzero state hinv)
    0 size (by omega) (initialState size) hinit
  simpa only [Nat.zero_add, build_address_index_eq_steps] using hfinal.1

theorem source_capacity_bound {size : Nat} (hsize : size ≤ 4294967296) :
    2 * size ≤ 8589934592 := by omega

theorem source_offset_bound {size i : Nat} (hsize : size ≤ 4294967296)
    (hi : i < size) : i ≤ 4294967295 := by omega

theorem source_slot_bound {size slot : Nat} (hsize : size ≤ 4294967296)
    (hslot : slot < 2 * size) : slot ≤ 8589934591 := by omega

end Leanisa.Proofs.I1b
