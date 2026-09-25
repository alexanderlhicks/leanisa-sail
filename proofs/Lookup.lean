import Memory

namespace Leanisa.Proofs
open Sail Leanisa.Functions

/-- The existing Sail exponentiation function, with a natural-number index. -/
def gAddress (i : Nat) : BitVec 64 := gpow (BitVec.ofNat 64 i)

/-- Explicit arithmetic and distinctness obligations for a finite memory domain.
No generator-order or field-arithmetic theorem is assumed globally. -/
structure GPowerDomain (n : Nat) : Prop where
  origin : gAddress 0 = 1
  successor : ∀ i, i + 1 < n → gAddress (i + 1) = advance (gAddress i)
  distinct : ∀ i j : Fin n, gAddress i.val = gAddress j.val → i = j

def vectorImage {n : Nat} (mem : Vector Word n) : Image n := mem.get

private def scanRange (n : Nat) : IntRange := { start := 0, stop := (n : Int) - 1 }

private def scanBody {n : Nat} (mem : Vector Word n) (target : BitVec 64)
    (i : Int) (_ : i ∈ scanRange n) (a : BitVec 64) :
    ExceptM memory_read (ForInStep (BitVec 64)) :=
  if a == target then .error ⟨mem[i]!, true⟩ else .ok (.yield (advance a))

private theorem loop_hits {n : Nat} (mem : Vector Word n) (domain : GPowerDomain n)
    (target : Fin n) (j : Nat) (hj : j ≤ target.val)
    (hs : ((j : Int) - (scanRange n).start) % (scanRange n).step = 0) :
    IntRange.forIn'.loop (m := ExceptM memory_read) (scanRange n) (scanBody mem (gAddress target.val))
      (gAddress j) (j : Int) hs = .error ⟨mem.get target, true⟩ := by
  have hin : (j : Int) ∈ scanRange n := by
    simp [scanRange, Membership.mem]
    omega
  rw [IntRange.forIn'.loop]
  simp only [dif_pos hin]
  by_cases heq : j = target.val
  · subst j
    simp [scanBody, Vector.get, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    rfl
  · have hjn : j < n := Nat.lt_of_le_of_lt hj target.isLt
    have hne : gAddress j ≠ gAddress target.val := by
      intro eq
      have := domain.distinct ⟨j, hjn⟩ target eq
      exact heq (congrArg Fin.val this)
    have hnext : j + 1 ≤ target.val := by omega
    have hstep := domain.successor j (Nat.lt_of_le_of_lt hnext target.isLt)
    simp only [scanBody, beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte]
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    rw [← hstep]
    exact loop_hits mem domain target (j + 1) hnext _
termination_by target.val - j

/-- A finite index resolves to its own cell in the actual extracted scan. -/
theorem read_memory_gAddress {n : Nat} (mem : Vector Word n) (domain : GPowerDomain n)
    (i : Fin n) :
    read_memory mem (gAddress i.val) = ⟨mem.get i, true⟩ := by
  simp only [read_memory, pure_bind, bind_pure, ExceptT.bind_throw]
  change ExceptM.run (do
    let _ ← IntRange.forIn'.loop (m := ExceptM memory_read) (scanRange n) (scanBody mem (gAddress i.val))
      (1 : BitVec 64) (0 : Int) (by simp [scanRange])
    pure ({ value := 0, valid := false } : memory_read)) = _
  rw [← domain.origin]
  have hit := loop_hits mem domain i 0 (Nat.zero_le _) (by simp [scanRange])
  exact congrArg
    (fun result : ExceptM memory_read (BitVec 64) => ExceptM.run (do
      let _ ← result
      pure ({ value := 0, valid := false } : memory_read))) hit

/-- Encoding a finite-index image as a vector preserves every admitted lookup. -/
theorem image_lookup {n : Nat} (image : Image n) (domain : GPowerDomain n) (i : Fin n) :
    read_memory (Vector.ofFn image) (gAddress i.val) = ⟨image i, true⟩ := by
  rw [read_memory_gAddress _ domain i]
  simp [Vector.get]

/-- Agreement with a partial memory transfers to the extracted memory reader. -/
theorem completed_cell_lookup {n : Nat} (mem : Vector Word n) (domain : GPowerDomain n)
    {memory : PartialMemory n} (finished : Completes memory (vectorImage mem))
    (i : Fin n) (v : Word) (fixed : memory i = some v)
    (address : BitVec 64) (maps : address = gAddress i.val) :
    read_memory mem address = ⟨v, true⟩ := by
  rw [maps, read_memory_gAddress mem domain i]
  have value : mem.get i = v := finished i v fixed
  rw [value]

private def fetchRange (n : Nat) : IntRange := { start := 0, stop := (n : Int) - 1 }

private def fetchBody {n : Nat} (program : Vector instruction n) (target : BitVec 64)
    (i : Int) (_ : i ∈ fetchRange n) (a : BitVec 64) :
    ExceptM (Option instruction) (ForInStep (BitVec 64)) :=
  if a == target then .error (some program[i]!) else .ok (.yield (advance a))

private theorem fetch_loop_hits {n : Nat} (program : Vector instruction n) (domain : GPowerDomain n)
    (target : Fin n) (j : Nat) (hj : j ≤ target.val)
    (hs : ((j : Int) - (fetchRange n).start) % (fetchRange n).step = 0) :
    IntRange.forIn'.loop (m := ExceptM (Option instruction)) (fetchRange n) (fetchBody program (gAddress target.val))
      (gAddress j) (j : Int) hs = .error (some (program.get target)) := by
  have hin : (j : Int) ∈ fetchRange n := by
    simp [fetchRange, Membership.mem]
    omega
  rw [IntRange.forIn'.loop]
  simp only [dif_pos hin]
  by_cases heq : j = target.val
  · subst j
    simp [fetchBody, Vector.get, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    rfl
  · have hjn : j < n := Nat.lt_of_le_of_lt hj target.isLt
    have hne : gAddress j ≠ gAddress target.val := by
      intro eq
      have := domain.distinct ⟨j, hjn⟩ target eq
      exact heq (congrArg Fin.val this)
    have hnext : j + 1 ≤ target.val := by omega
    have hstep := domain.successor j (Nat.lt_of_le_of_lt hnext target.isLt)
    simp only [fetchBody, beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte]
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    rw [← hstep]
    exact fetch_loop_hits program domain target (j + 1) hnext _
termination_by target.val - j

/-- A finite index resolves to its own cell in the actual extracted program scan. -/
theorem fetch_gAddress {n : Nat} (program : Vector instruction n) (domain : GPowerDomain n)
    (i : Fin n) :
    fetch program (gAddress i.val) = some (program.get i) := by
  simp only [fetch, pure_bind, bind_pure, ExceptT.bind_throw]
  change ExceptM.run (do
    let _ ← IntRange.forIn'.loop (m := ExceptM (Option instruction)) (fetchRange n) (fetchBody program (gAddress i.val))
      (1 : BitVec 64) (0 : Int) (by simp [fetchRange])
    pure (none : Option instruction)) = _
  rw [← domain.origin]
  have hit := fetch_loop_hits program domain i 0 (Nat.zero_le _) (by simp [fetchRange])
  exact congrArg
    (fun result : ExceptM (Option instruction) (BitVec 64) => ExceptM.run (do
      let _ ← result
      pure (none : Option instruction))) hit

end Leanisa.Proofs

#print axioms Leanisa.Proofs.read_memory_gAddress
#print axioms Leanisa.Proofs.image_lookup
#print axioms Leanisa.Proofs.completed_cell_lookup

#print axioms Leanisa.Proofs.fetch_gAddress
