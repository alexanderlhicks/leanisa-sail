import CircularProbe

namespace Leanisa.Proofs.I1b
open Sail Leanisa.Functions Leanisa.Proofs.I1a

private def builderRange (size : Nat) : IntRange :=
  { start := 0, stop := (size : Int) - 1 }

def emptyEntry : address_entry := ⟨0#64, 0⟩

def initialState (size : Nat) :
    BitVec 64 × Vector address_entry (2 * size) :=
  (1#64, vectorInit emptyEntry)

private def builderBody (size : Nat) (i : Int) (_ : i ∈ builderRange size)
    (state : BitVec 64 × Vector address_entry (2 * size)) :
    Id (ForInStep (BitVec 64 × Vector address_entry (2 * size))) :=
  let address := state.1
  let index := state.2
  let index : Vector address_entry (2 * size) :=
    match address_slot index address with
    | .some slot =>
      if (slot <b Vector.length index : Bool) then
        vectorUpdate index slot { address := address, offset := i }
      else index
    | none => index
  pure (.yield (advance address, index))

def builderStep (size i : Nat)
    (state : BitVec 64 × Vector address_entry (2 * size)) :
    BitVec 64 × Vector address_entry (2 * size) :=
  let address := state.1
  let index := state.2
  let index : Vector address_entry (2 * size) :=
    match address_slot index address with
    | .some slot =>
      if (slot <b Vector.length index : Bool) then
        vectorUpdate index slot { address := address, offset := i }
      else index
    | none => index
  (advance address, index)

private theorem builderBody_nat (size i : Nat) (hi : (i : Int) ∈ builderRange size)
    (state : BitVec 64 × Vector address_entry (2 * size)) :
    builderBody size i hi state = pure (.yield (builderStep size i state)) := by
  simp only [builderBody, builderStep]
  rfl

def builderSteps (size : Nat) : Nat → Nat →
    (BitVec 64 × Vector address_entry (2 * size)) →
    (BitVec 64 × Vector address_entry (2 * size))
  | _, 0, state => state
  | i, k + 1, state => builderSteps size (i + 1) k (builderStep size i state)

private theorem builder_unfold (size : Nat) :
    build_address_index size =
      (IntRange.forIn'.loop (m := Id) (builderRange size)
        (builderBody size) (initialState size) (0 : Int)
        (by simp [builderRange])).2 := by
  unfold build_address_index
  simp only [ForIn.forIn, ForIn'.forIn', IntRange.forIn']
  simp only [builderRange, initialState, emptyEntry, vectorInit, Vector.length]
  rfl

private theorem builder_loop_eq (size j : Nat) (hj : j ≤ size)
    (state : BitVec 64 × Vector address_entry (2 * size))
    (hs : ((j : Int) - (builderRange size).start) % (builderRange size).step = 0) :
    IntRange.forIn'.loop (m := Id) (builderRange size) (builderBody size)
      state j hs = builderSteps size j (size - j) state := by
  rw [IntRange.forIn'.loop]
  by_cases hlt : j < size
  · have hin : (j : Int) ∈ builderRange size := by
      simp [builderRange, Membership.mem]
      omega
    simp only [dif_pos hin]
    have hsub : size - j = (size - (j + 1)) + 1 := by omega
    rw [hsub, builderBody_nat size j hin]
    simp only [builderSteps]
    exact builder_loop_eq size (j + 1) (by omega) (builderStep size j state) _
  · have heq : j = size := by omega
    have hout : ¬ (j : Int) ∈ builderRange size := by
      simp [builderRange, Membership.mem]
      omega
    simp only [dif_neg hout]
    simp [heq, builderSteps]
    rfl
termination_by size - j

theorem build_address_index_eq_steps (size : Nat) :
    build_address_index size = (builderSteps size 0 size (initialState size)).2 := by
  rw [builder_unfold]
  have hloop := builder_loop_eq size 0 (by omega) (initialState size)
    (by simp [builderRange])
  simp only [Nat.sub_zero] at hloop
  exact congrArg Prod.snd hloop

theorem builderSteps_invariant (size : Nat)
    (P : Nat → (BitVec 64 × Vector address_entry (2 * size)) → Prop)
    (step : ∀ k, k < size → ∀ state, P k state →
      P (k + 1) (builderStep size k state))
    (k fuel : Nat) (hbound : k + fuel ≤ size)
    (state : BitVec 64 × Vector address_entry (2 * size))
    (hstate : P k state) :
    P (k + fuel) (builderSteps size k fuel state) := by
  induction fuel generalizing k state with
  | zero => simpa [builderSteps] using hstate
  | succ fuel ih =>
    have hk : k < size := by omega
    have hnext := step k hk state hstate
    have htail := ih (k + 1) (by omega) (builderStep size k state) hnext
    simpa [builderSteps, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

end Leanisa.Proofs.I1b
