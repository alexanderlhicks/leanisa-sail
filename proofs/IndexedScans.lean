import BuilderCorrectness

namespace Leanisa.Proofs.I1c1
open Sail Leanisa.Functions Leanisa.Proofs

def scanRange (n : Nat) : IntRange :=
  { start := 0, stop := (n : Int) - 1 }

def scanReadBody {n : Nat} (mem : Vector Word n) (address : BitVec 64)
    (i : Int) (_ : i ∈ scanRange n) (current : BitVec 64) :
    ExceptM memory_read (ForInStep (BitVec 64)) :=
  if current == address then .error ⟨mem[i]!, true⟩
  else .ok (.yield (advance current))

def scanFetchBody {n : Nat} (program : Vector Leanisa.instruction n)
    (address : BitVec 64) (i : Int) (_ : i ∈ scanRange n)
    (current : BitVec 64) :
    ExceptM (Option Leanisa.instruction) (ForInStep (BitVec 64)) :=
  if current == address then .error (some program[i]!)
  else .ok (.yield (advance current))

theorem GPowerDomain.restrict {n N : Nat} (domain : GPowerDomain N)
    (covers : n ≤ N) : GPowerDomain n := by
  refine ⟨domain.origin, ?_, ?_⟩
  · intro i hi
    exact domain.successor i (by omega)
  · intro i j equal
    have h := domain.distinct (⟨i.val, by omega⟩ : Fin N)
      (⟨j.val, by omega⟩ : Fin N) equal
    have hval : i.val = j.val := congrArg (fun x : Fin N => x.val) h
    exact Fin.ext hval

private theorem scan_read_loop_misses {n : Nat} (mem : Vector Word n)
    (domain : GPowerDomain n) (address : BitVec 64)
    (absent : ∀ i : Fin n, address ≠ gAddress i.val)
    (j : Nat) (hj : j ≤ n) (current : BitVec 64)
    (hcurrent : j < n → current = gAddress j)
    (hs : ((j : Int) - (scanRange n).start) % (scanRange n).step = 0) :
    ExceptM.run (do
      let _ ← IntRange.forIn'.loop (m := ExceptM memory_read) (scanRange n)
        (scanReadBody mem address) current (j : Int) hs
      pure ({ value := 0, valid := false } : memory_read)) =
      ({ value := 0, valid := false } : memory_read) := by
  rw [IntRange.forIn'.loop]
  by_cases hlt : j < n
  · have hin : (j : Int) ∈ scanRange n := by
      simp [scanRange, Membership.mem]
      omega
    simp only [dif_pos hin]
    have hne : current ≠ address := by
      rw [hcurrent hlt]
      exact (absent ⟨j, hlt⟩).symm
    simp only [scanReadBody, beq_eq_false_iff_ne.mpr hne,
      Bool.false_eq_true, ↓reduceIte]
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    apply scan_read_loop_misses mem domain address absent (j + 1) (by omega)
      (advance current)
    intro hnext
    rw [hcurrent hlt]
    exact (domain.successor j hnext).symm
  · have hout : ¬ (j : Int) ∈ scanRange n := by
      simp [scanRange, Membership.mem]
      omega
    simp only [dif_neg hout]
    rfl
termination_by n - j

theorem read_memory_miss {n : Nat} (mem : Vector Word n)
    (domain : GPowerDomain n) (address : BitVec 64)
    (absent : ∀ i : Fin n, address ≠ gAddress i.val) :
    read_memory mem address = ⟨0#192, false⟩ := by
  simp only [read_memory, pure_bind, bind_pure, ExceptT.bind_throw]
  change ExceptM.run (do
    let _ ← IntRange.forIn'.loop (m := ExceptM memory_read) (scanRange n)
      (scanReadBody mem address) (1 : BitVec 64) (0 : Int)
      (by simp [scanRange])
    pure ({ value := 0, valid := false } : memory_read)) = _
  exact scan_read_loop_misses mem domain address absent 0 (by omega) 1
    (fun _ => domain.origin.symm) (by simp [scanRange])

private theorem scan_fetch_loop_misses {n : Nat}
    (program : Vector Leanisa.instruction n) (domain : GPowerDomain n)
    (address : BitVec 64)
    (absent : ∀ i : Fin n, address ≠ gAddress i.val)
    (j : Nat) (hj : j ≤ n) (current : BitVec 64)
    (hcurrent : j < n → current = gAddress j)
    (hs : ((j : Int) - (scanRange n).start) % (scanRange n).step = 0) :
    ExceptM.run (do
      let _ ← IntRange.forIn'.loop (m := ExceptM (Option Leanisa.instruction))
        (scanRange n) (scanFetchBody program address) current (j : Int) hs
      pure (none : Option Leanisa.instruction)) = none := by
  rw [IntRange.forIn'.loop]
  by_cases hlt : j < n
  · have hin : (j : Int) ∈ scanRange n := by
      simp [scanRange, Membership.mem]
      omega
    simp only [dif_pos hin]
    have hne : current ≠ address := by
      rw [hcurrent hlt]
      exact (absent ⟨j, hlt⟩).symm
    simp only [scanFetchBody, beq_eq_false_iff_ne.mpr hne,
      Bool.false_eq_true, ↓reduceIte]
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    apply scan_fetch_loop_misses program domain address absent (j + 1) (by omega)
      (advance current)
    intro hnext
    rw [hcurrent hlt]
    exact (domain.successor j hnext).symm
  · have hout : ¬ (j : Int) ∈ scanRange n := by
      simp [scanRange, Membership.mem]
      omega
    simp only [dif_neg hout]
    rfl
termination_by n - j

theorem fetch_miss {n : Nat} (program : Vector Leanisa.instruction n)
    (domain : GPowerDomain n) (address : BitVec 64)
    (absent : ∀ i : Fin n, address ≠ gAddress i.val) :
    fetch program address = none := by
  simp only [fetch, pure_bind, bind_pure, ExceptT.bind_throw]
  change ExceptM.run (do
    let _ ← IntRange.forIn'.loop (m := ExceptM (Option Leanisa.instruction))
      (scanRange n) (scanFetchBody program address) (1 : BitVec 64)
      (0 : Int) (by simp [scanRange])
    pure (none : Option Leanisa.instruction)) = _
  exact scan_fetch_loop_misses program domain address absent 0 (by omega) 1
    (fun _ => domain.origin.symm) (by simp [scanRange])

end Leanisa.Proofs.I1c1
