import Leanisa

/-!
A partial witness-memory policy, separate from Rust's current executor.
An eager observation fixes a value; a deferred equality does not observe one.
The address domain is finite and bounds-checked by construction. Lookup.lean
connects it to Sail's g-power lookup under explicit arithmetic hypotheses.
Connection to the upstream instruction trace remains separate.
-/
namespace Leanisa.Proofs

abbrev Word := BitVec 192
abbrev PartialMemory (n : Nat) := Fin n → Option Word
abbrev Image (n : Nat) := Fin n → Word

/-- Every fixed cell keeps its value as the witness is extended. -/
def Extends {n : Nat} (before after : PartialMemory n) : Prop :=
  ∀ a v, before a = some v → after a = some v

/-- A completed image agrees with every fixed cell. -/
def Completes {n : Nat} (memory : PartialMemory n) (image : Image n) : Prop :=
  ∀ a v, memory a = some v → image a = v

/-- Assign advice, an instruction result, or an observed value consistently. -/
def assign {n : Nat} (memory : PartialMemory n) (a : Fin n) (v : Word) :
    Option (PartialMemory n) :=
  match memory a with
  | none => some (fun b => if b = a then some v else memory b)
  | some old => if old = v then some memory else none

/-- A deterministic zero-default observation commits the zero it returns. -/
def observeZero {n : Nat} (memory : PartialMemory n) (a : Fin n) :
    Word × PartialMemory n :=
  match memory a with
  | some v => (v, memory)
  | none => (0, fun b => if b = a then some 0 else memory b)

/-- Completion can choose zero for cells no eager observation has fixed. -/
def completeZero {n : Nat} (memory : PartialMemory n) : Image n :=
  fun a => (memory a).getD 0

/-- Pending Cell-mode DEREF constraints are checked on the completed image.
They are not eager zero observations of either endpoint. -/
def Resolves {n : Nat} (equalities : List (Fin n × Fin n)) (image : Image n) : Prop :=
  ∀ pair ∈ equalities, image pair.1 = image pair.2

@[simp] theorem extends_refl {n : Nat} (memory : PartialMemory n) :
    Extends memory memory := by
  intro a v h
  exact h

theorem extends_trans {n : Nat} {m₀ m₁ m₂ : PartialMemory n}
    (h₁ : Extends m₀ m₁) (h₂ : Extends m₁ m₂) : Extends m₀ m₂ := by
  intro a v h
  exact h₂ a v (h₁ a v h)

theorem completion_preserves_prefix {n : Nat} {before after : PartialMemory n}
    {image : Image n} (h : Extends before after) (hc : Completes after image) :
    Completes before image := by
  intro a v hv
  exact hc a v (h a v hv)

theorem assign_extends {n : Nat} {memory next : PartialMemory n}
    {a : Fin n} {v : Word} (h : assign memory a v = some next) :
    Extends memory next := by
  unfold assign at h
  split at h
  next empty =>
    cases h
    intro b old hb
    by_cases eq : b = a
    · subst b
      simp [empty] at hb
    · simp [eq, hb]
  next old fixed =>
    split at h
    · cases h
      exact extends_refl _
    · cases h

theorem assign_fixes_value {n : Nat} {memory next : PartialMemory n}
    {a : Fin n} {v : Word} (h : assign memory a v = some next) : next a = some v := by
  unfold assign at h
  split at h
  next empty => cases h; simp
  next old fixed =>
    split at h
    next equal => cases h; simpa [equal] using fixed
    next different => cases h

theorem observe_extends {n : Nat} (memory : PartialMemory n) (a : Fin n) :
    Extends memory (observeZero memory a).2 := by
  unfold observeZero
  split
  next fixed => exact extends_refl _
  next empty =>
    intro b v hb
    by_cases eq : b = a
    · subst b
      simp [empty] at hb
    · simp [eq, hb]

theorem observe_fixes_value {n : Nat} (memory : PartialMemory n) (a : Fin n) :
    (observeZero memory a).2 a = some (observeZero memory a).1 := by
  unfold observeZero
  split <;> simp_all

theorem completeZero_completes {n : Nat} (memory : PartialMemory n) :
    Completes memory (completeZero memory) := by
  intro a v h
  simp [completeZero, h]

/-- A later compatible completion preserves every eager observation, including
zero observed before any explicit assignment. -/
theorem observed_value_in_final_image {n : Nat} (memory : PartialMemory n)
    (a : Fin n) {later : PartialMemory n} {image : Image n}
    (growth : Extends (observeZero memory a).2 later)
    (finished : Completes later image) :
    image a = (observeZero memory a).1 := by
  exact finished a _ (growth a _ (observe_fixes_value memory a))

/-- Finite executions of the memory policy, including arbitrary compatible
advice assignments. Deferred equalities are obligations on completion. -/
inductive Evolves {n : Nat} : PartialMemory n → PartialMemory n → Prop where
  | refl (memory) : Evolves memory memory
  | assignment {before after} (a v) (ok : assign before a v = some after) :
      Evolves before after
  | observation (memory a) : Evolves memory (observeZero memory a).2
  | trans {before middle after} : Evolves before middle → Evolves middle after →
      Evolves before after

theorem execution_extends {n : Nat} {before after : PartialMemory n}
    (execution : Evolves before after) : Extends before after := by
  induction execution with
  | refl memory => exact extends_refl memory
  | assignment a v ok => exact assign_extends ok
  | observation memory a => exact observe_extends memory a
  | trans first second ih₁ ih₂ => exact extends_trans ih₁ ih₂

theorem execution_preserves_observation {n : Nat} (memory : PartialMemory n)
    (a : Fin n) {later : PartialMemory n} {image : Image n}
    (execution : Evolves (observeZero memory a).2 later)
    (finished : Completes later image) :
    image a = (observeZero memory a).1 := by
  exact observed_value_in_final_image memory a (execution_extends execution) finished

theorem deferred_equality_allows_any_value (v : Word) :
    Resolves [(0, 1)] (fun (_ : Fin 2) => v) := by
  simp [Resolves]

/-- Explicit failure for the pattern that Rust currently accepts. -/
theorem rejects_changed_observation {n : Nat} (memory : PartialMemory n) (a : Fin n)
    (v : Word) (different : v ≠ (observeZero memory a).1) :
    assign (observeZero memory a).2 a v = none := by
  simp [assign, observe_fixes_value, Ne.symm different]

/-- The weak write-once condition alone does not preserve an eager zero read. -/
theorem weak_read_counterexample :
    let empty : PartialMemory 1 := fun _ => none
    let a : Fin 1 := ⟨0, by decide⟩
    ∃ later, assign empty a 1 = some later ∧
      completeZero later a ≠ (empty a).getD 0 := by
  refine ⟨fun _ => some 1, ?_, ?_⟩
  · simp [assign]
    funext b
    have hb : b = 0 := by apply Fin.ext; omega
    simp [hb]
  · decide

-- Small theorems about the actual Sail extraction, not a second field model.
open Leanisa.Functions

theorem embedded_base_has_zero_extension_limbs (x : BitVec 64) :
    in_k (embed_k x) = true := by
  simp only [in_k, embed_k, Sail.BitVec.extractLsb, beq_iff_eq]
  exact BitVec.extractLsb'_append_eq_left

end Leanisa.Proofs

#print axioms Leanisa.Proofs.execution_preserves_observation
#print axioms Leanisa.Proofs.rejects_changed_observation
#print axioms Leanisa.Proofs.weak_read_counterexample
#print axioms Leanisa.Proofs.embedded_base_has_zero_extension_limbs
