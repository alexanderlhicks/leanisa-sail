import Instructions

namespace Leanisa.Proofs
open Sail Leanisa.Functions

/-- Registers with which the extracted runner starts. -/
def initialState : machine_state := ⟨1, 1⟩

/-- Public-input binding and size checks performed before any instruction. -/
structure ValidInstance {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) : Prop where
  programPositive : 1 ≤ p
  programPower : power_of_two p = true
  memoryPower : power_of_two m = true
  memoryLower : 65536 ≤ m
  memoryUpper : m ≤ 4294967296
  programUpper : p ≤ 4294967296
  publicLow : mem[0]! = (0#64 +++ Sail.BitVec.extractLsb publicInput 127 0)
  publicHigh : mem[1]! = (0#64 +++ Sail.BitVec.extractLsb publicInput 255 128)

/-- The runner's unexecuted sentinel, expressed with exactly its extracted arithmetic. -/
def sentinel {p : Nat} (program : Vector instruction p) : BitVec 64 :=
  gpow (get_slice_int 64 ((Vector.length program) -i 1) 0)

private def runRange (fuel : Nat) : IntRange := { start := 0, stop := fuel }

private def runBody {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (fuel : Nat) (i : Int) (_ : i ∈ runRange fuel) (s : machine_state) :
    ExceptM step_result (ForInStep machine_state) :=
  if s.pc == sentinel program then do
    let next ← throw (⟨s, if s.fp == 1 then .Halted else .BadValue⟩ : step_result)
    pure (.yield next)
  else do
    let next ← (
      if i == (fuel : Int) then throw (⟨s, .OutOfFuel⟩ : step_result)
      else match fetch program s.pc with
        | none => throw (⟨s, .BadAccess⟩ : step_result)
        | some ins =>
          let result := step s ins mem
          if result.verdict != .Running then throw result else pure result.state
      : ExceptM step_result machine_state)
    pure (.yield next)

/-- A successful finite prefix, with no eventual-halting requirement. It can
describe any bounded prefix of a genuinely looping execution. -/
structure StepPrefix {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (states : Nat → machine_state) (steps : Nat) : Prop where
  initial : states 0 = initialState
  progress : ∀ i, i < steps →
    (states i).pc ≠ sentinel program ∧
    ∃ ins, fetch program (states i).pc = some ins ∧
      step (states i) ins mem = ⟨states (i + 1), .Running⟩

/-- A finite chain of concrete successful instruction results ending at the sentinel. -/
structure StepTrace {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (states : Nat → machine_state) (steps : Nat) : Prop where
  initial : states 0 = initialState
  progress : ∀ i, i < steps →
    (states i).pc ≠ sentinel program ∧
    ∃ ins, fetch program (states i).pc = some ins ∧
      step (states i) ins mem = ⟨states (i + 1), .Running⟩
  terminal : (states steps).pc = sentinel program

theorem StepTrace.to_prefix {p m : Nat} {program : Vector instruction p} {mem : Vector Word m}
    {states : Nat → machine_state} {steps : Nat} (trace : StepTrace program mem states steps) :
    StepPrefix program mem states steps := ⟨trace.initial, trace.progress⟩

theorem StepPrefix.terminal_trace {p m : Nat} {program : Vector instruction p}
    {mem : Vector Word m} {states : Nat → machine_state} {steps : Nat}
    (chain : StepPrefix program mem states steps)
    (terminal : (states steps).pc = sentinel program) :
    StepTrace program mem states steps := ⟨chain.initial, chain.progress, terminal⟩

private theorem loop_composes {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (fuel stop : Nat) (states : Nat → machine_state)
    (result : step_result) (bounded : stop ≤ fuel)
    (progress : ∀ i, i < stop →
      (states i).pc ≠ sentinel program ∧
      ∃ ins, fetch program (states i).pc = some ins ∧
        step (states i) ins mem = ⟨states (i + 1), .Running⟩)
    (terminal : ∀ h, runBody program mem fuel (stop : Int) h (states stop) = .error result)
    (j : Nat) (hj : j ≤ stop)
    (hs : ((j : Int) - (runRange fuel).start) % (runRange fuel).step = 0) :
    IntRange.forIn'.loop (m := ExceptM step_result) (runRange fuel) (runBody program mem fuel)
      (states j) (j : Int) hs = .error result := by
  have hin : (j : Int) ∈ runRange fuel := by
    simp [runRange, Membership.mem]
    omega
  rw [IntRange.forIn'.loop]
  simp only [dif_pos hin]
  by_cases eq : j = stop
  · subst j
    simp only [terminal, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    rfl
  · have hlt : j < stop := by omega
    obtain ⟨notHalt, ins, fetched, stepped⟩ := progress j hlt
    have notFuel : (j : Int) ≠ (fuel : Int) := by omega
    simp only [runBody, beq_eq_false_iff_ne.mpr notHalt, Bool.false_eq_true, ↓reduceIte,
      beq_eq_false_iff_ne.mpr notFuel, fetched, stepped]
    simp only [show (status.Running != status.Running) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    exact loop_composes program mem fuel stop states result bounded progress terminal
      (j + 1) (by omega) _
termination_by stop - j

private theorem run_from_loop {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel : Nat)
    (valid : ValidInstance program mem publicInput) (result : step_result)
    (loop : IntRange.forIn'.loop (m := ExceptM step_result) (runRange fuel)
      (runBody program mem fuel) initialState (0 : Int) (by simp [runRange]) = .error result) :
    run program mem publicInput fuel = result := by
  simp only [run, pure_bind]
  simp only [Vector.length, valid.programPower, valid.memoryPower,
    valid.publicLow, valid.publicHigh]
  have lower : ¬ m < 65536 := by have := valid.memoryLower; omega
  have upper : ¬ m > 4294967296 := by have := valid.memoryUpper; omega
  have progUpper : ¬ p > 4294967296 := by have := valid.programUpper; omega
  simp only [Bool.not_true, bne_self_eq_false, Bool.or_false,
    decide_eq_false lower, decide_eq_false upper, decide_eq_false progUpper,
    Bool.false_eq_true, ↓reduceIte, bind_pure]
  change ExceptM.run (do
    let s ← IntRange.forIn'.loop (m := ExceptM step_result) (runRange fuel)
      (runBody program mem fuel) initialState (0 : Int) (by simp [runRange])
    pure ({ state := s, verdict := .OutOfFuel } : step_result)) = result
  rw [loop]
  rfl

/-- Halting is checked before fuel exhaustion and before fetching the sentinel.
A non-unit final frame is rejected even when the PC is at the sentinel. -/
theorem run_trace_terminal {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel steps : Nat)
    (valid : ValidInstance program mem publicInput) (states : Nat → machine_state)
    (trace : StepTrace program mem states steps) (enough : steps ≤ fuel) :
    run program mem publicInput fuel =
      ⟨states steps, if (states steps).fp == 1 then .Halted else .BadValue⟩ := by
  apply run_from_loop program mem publicInput fuel valid
  rw [← trace.initial]
  apply loop_composes program mem fuel steps states _ enough trace.progress
  · intro h
    simp only [runBody, trace.terminal, beq_self_eq_true, ↓reduceIte]
    rfl
  · omega

/-- Insufficient fuel returns precisely the registers after that many successful steps. -/
theorem run_trace_out_of_fuel {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel steps : Nat)
    (valid : ValidInstance program mem publicInput) (states : Nat → machine_state)
    (trace : StepTrace program mem states steps) (short : fuel < steps) :
    run program mem publicInput fuel = ⟨states fuel, .OutOfFuel⟩ := by
  apply run_from_loop program mem publicInput fuel valid
  rw [← trace.initial]
  apply loop_composes program mem fuel fuel states _ (Nat.le_refl _)
  · intro i hi
    exact trace.progress i (Nat.lt_trans hi short)
  · intro h
    have notHalt := (trace.progress fuel short).1
    simp only [runBody, beq_eq_false_iff_ne.mpr notHalt, Bool.false_eq_true, ↓reduceIte,
      beq_self_eq_true]
    rfl
  · omega

/-- A nonterminal endpoint exhausts its budget, without requiring a future halt.
The chosen budget can be any length within the supplied successful chain. -/
theorem run_prefix_out_of_fuel {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel steps : Nat)
    (valid : ValidInstance program mem publicInput) (states : Nat → machine_state)
    (chain : StepPrefix program mem states steps) (bounded : fuel ≤ steps)
    (nonterminal : (states fuel).pc ≠ sentinel program) :
    run program mem publicInput fuel = ⟨states fuel, .OutOfFuel⟩ := by
  apply run_from_loop program mem publicInput fuel valid
  rw [← chain.initial]
  apply loop_composes program mem fuel fuel states _ (Nat.le_refl _)
  · intro i hi
    exact chain.progress i (Nat.lt_of_lt_of_le hi bounded)
  · intro h
    simp only [runBody, beq_eq_false_iff_ne.mpr nonterminal, Bool.false_eq_true,
      ↓reduceIte, beq_self_eq_true]
    rfl
  · omega

/-- Every strict interior fuel boundary of a successful prefix is nonterminal. -/
theorem run_prefix_short {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel steps : Nat)
    (valid : ValidInstance program mem publicInput) (states : Nat → machine_state)
    (chain : StepPrefix program mem states steps) (short : fuel < steps) :
    run program mem publicInput fuel = ⟨states fuel, .OutOfFuel⟩ := by
  exact run_prefix_out_of_fuel program mem publicInput fuel steps valid states chain
    (Nat.le_of_lt short) (chain.progress fuel short).1

/-- A terminal prefix halts before checking fuel or fetching the sentinel. -/
theorem run_prefix_terminal {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel steps : Nat)
    (valid : ValidInstance program mem publicInput) (states : Nat → machine_state)
    (chain : StepPrefix program mem states steps)
    (terminal : (states steps).pc = sentinel program) (enough : steps ≤ fuel) :
    run program mem publicInput fuel =
      ⟨states steps, if (states steps).fp == 1 then .Halted else .BadValue⟩ := by
  exact run_trace_terminal program mem publicInput fuel steps valid states
    (chain.terminal_trace terminal) enough

/-- Fetch failure after a successful prefix is reached only with surplus fuel. -/
theorem run_prefix_bad_fetch {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel steps : Nat)
    (valid : ValidInstance program mem publicInput) (states : Nat → machine_state)
    (chain : StepPrefix program mem states steps)
    (nonterminal : (states steps).pc ≠ sentinel program)
    (missing : fetch program (states steps).pc = none) (surplus : steps < fuel) :
    run program mem publicInput fuel = ⟨states steps, .BadAccess⟩ := by
  apply run_from_loop program mem publicInput fuel valid
  rw [← chain.initial]
  apply loop_composes program mem fuel steps states _ (Nat.le_of_lt surplus) chain.progress
  · intro h
    have notFuel : (steps : Int) ≠ (fuel : Int) := by omega
    simp only [runBody, beq_eq_false_iff_ne.mpr nonterminal, Bool.false_eq_true,
      ↓reduceIte, beq_eq_false_iff_ne.mpr notFuel, missing]
    rfl
  · omega

/-- A failed concrete instruction result is preserved after a successful chain.
This composes error semantics; it does not derive rejection from a failed policy. -/
theorem run_prefix_failed_step {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel steps : Nat)
    (valid : ValidInstance program mem publicInput) (states : Nat → machine_state)
    (chain : StepPrefix program mem states steps)
    (nonterminal : (states steps).pc ≠ sentinel program) (ins : instruction)
    (fetched : fetch program (states steps).pc = some ins) (result : step_result)
    (failed : step (states steps) ins mem = result) (notRunning : result.verdict ≠ .Running)
    (surplus : steps < fuel) : run program mem publicInput fuel = result := by
  apply run_from_loop program mem publicInput fuel valid
  rw [← chain.initial]
  apply loop_composes program mem fuel steps states _ (Nat.le_of_lt surplus) chain.progress
  · intro h
    have notFuel : (steps : Int) ≠ (fuel : Int) := by omega
    have rejected : (result.verdict != status.Running) = true := by
      cases hv : result.verdict <;> simp_all <;> rfl
    simp only [runBody, beq_eq_false_iff_ne.mpr nonterminal, Bool.false_eq_true,
      ↓reduceIte, beq_eq_false_iff_ne.mpr notFuel, fetched, failed, rejected]
    rfl
  · omega

/-- Exactly the failures tested by Sail before entering its execution loop. -/
def InvalidInstance {p m : Nat} (_program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) : Prop :=
  power_of_two p = false ∨ power_of_two m = false ∨ m < 65536 ∨
  m > 4294967296 ∨ p > 4294967296 ∨
  mem[0]! ≠ (0#64 +++ Sail.BitVec.extractLsb publicInput 127 0) ∨
  mem[1]! ≠ (0#64 +++ Sail.BitVec.extractLsb publicInput 255 128)

theorem run_invalid_instance {p m : Nat} (program : Vector instruction p)
    (mem : Vector Word m) (publicInput : BitVec 256) (fuel : Nat)
    (invalid : InvalidInstance program mem publicInput) :
    run program mem publicInput fuel = ⟨initialState, .BadInstance⟩ := by
  rcases invalid with h | h | h | h | h | h | h <;>
    simp [run, Vector.length, h, initialState, ExceptM.run]

/-- One admissible SET/XOR operation. Operand indices are bounded, and effective
address equations remain premises rather than assumed arithmetic theorems. -/
inductive SetXorStep {m : Nat} (s : machine_state) :
    PartialMemory m → instruction → PartialMemory m → Prop where
  | set {before after} (offset : BitVec 64) (i : Fin m) (v : Word)
      (maps : kmul s.fp offset = gAddress i.val)
      (assigned : assign before i v = some after) :
      SetXorStep s before (.Set (offset, v)) after
  | xor {before after} (oa ob oc : BitVec 64) (a b c : Fin m)
      (maps_a : kmul s.fp oa = gAddress a.val)
      (maps_b : kmul s.fp ob = gAddress b.val)
      (maps_c : kmul s.fp oc = gAddress c.val)
      (assigned : xorAssign before a b c = some after) :
      SetXorStep s before (.Xor (oa, ob, oc)) after

theorem SetXorStep.evolves {m : Nat} {s : machine_state}
    {before after : PartialMemory m} {ins : instruction}
    (operation : SetXorStep s before ins after) : Evolves before after := by
  cases operation with
  | set offset i v maps assigned => exact .assignment i v assigned
  | xor oa ob oc a b c maps_a maps_b maps_c assigned =>
    exact .trans (.observation before a)
      (.trans (.observation (observeZero before a).2 b) (.assignment c _ assigned))

theorem SetXorStep.simulates {m : Nat} (mem : Vector Word m) (domain : GPowerDomain m)
    {s : machine_state} {before after later : PartialMemory m} {ins : instruction}
    (operation : SetXorStep s before ins after) (continuation : Evolves after later)
    (finished : Completes later (vectorImage mem)) :
    step s ins mem = ⟨advancedState s, .Running⟩ := by
  cases operation with
  | set offset i v maps assigned =>
    exact assignment_simulates_set mem domain s offset i v maps assigned continuation finished
  | xor oa ob oc a b c maps_a maps_b maps_c assigned =>
    exact xor_policy_simulates_step mem domain s oa ob oc a b c maps_a maps_b maps_c
      assigned continuation finished

/-- Compatible operations compose to give the continuation needed by each local proof. -/
theorem evolves_suffix {m : Nat} (memories : Nat → PartialMemory m) (steps : Nat)
    (growth : ∀ i, i < steps → Evolves (memories i) (memories (i + 1)))
    (j : Nat) (bounded : j ≤ steps) : Evolves (memories j) (memories steps) := by
  by_cases eq : j = steps
  · subst j; exact .refl _
  · exact .trans (growth j (by omega))
      (evolves_suffix memories steps growth (j + 1) (by omega))
termination_by steps - j

/-- Registers for the straight-line fragment; arithmetic relating g-powers to
successive PCs is supplied by the program's GPowerDomain hypothesis. -/
def registersAt (i : Nat) : machine_state := ⟨gAddress i, 1⟩

/-- Every instruction before the sentinel follows the compatible memory policy.
The sentinel instruction itself is deliberately unconstrained. -/
def SetXorFragment {p m : Nat} (program : Vector instruction p)
    (memories : Nat → PartialMemory m) : Prop :=
  ∀ i (hi : i < p - 1), SetXorStep (registersAt i) (memories i)
    (program.get ⟨i, by omega⟩) (memories (i + 1))

theorem sentinel_gAddress {p : Nat} (program : Vector instruction p) (positive : 1 ≤ p) :
    sentinel program = gAddress (p - 1) := by
  simp only [sentinel, Vector.length, gAddress, get_slice_int]
  have subtract : (p : Int) - 1 = ((p - 1 : Nat) : Int) := by omega
  rw [subtract]
  congr 1
  simp only [BitVec.ofInt_natCast]
  change (BitVec.ofNat 65 (p - 1)).setWidth 64 = BitVec.ofNat 64 (p - 1)
  exact BitVec.setWidth_ofNat_of_le (by decide) _

/-- Successful non-branching steps construct the concrete trace. Program fetch,
PC progression, and sentinel exclusion follow from the program address domain. -/
theorem straightline_trace {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (positive : 1 ≤ p) (programDomain : GPowerDomain p)
    (successful : ∀ i (hi : i < p - 1),
      step (registersAt i) (program.get ⟨i, by omega⟩) mem =
        ⟨advancedState (registersAt i), .Running⟩) :
    StepTrace program mem registersAt (p - 1) := by
  constructor
  · simp [registersAt, initialState, programDomain.origin]
  · intro i hi
    have hip : i < p := by omega
    constructor
    · intro eq
      have addresses : gAddress i = gAddress (p - 1) := by
        simpa [registersAt, sentinel_gAddress program positive] using eq
      have indexEq : i = p - 1 := congrArg Fin.val (programDomain.distinct ⟨i, hip⟩ ⟨p - 1, by omega⟩ addresses)
      omega
    · refine ⟨program.get ⟨i, hip⟩, fetch_gAddress program programDomain ⟨i, hip⟩, ?_⟩
      have next : advancedState (registersAt i) = registersAt (i + 1) := by
        simp [advancedState, registersAt, programDomain.successor i (by omega)]
      simpa only [next] using successful i hi
  · exact (sentinel_gAddress program positive).symm

/-- Admissible SET/XOR operations and a compatible final image construct the
concrete trace; its fetch and step results are conclusions, not hypotheses. -/
theorem set_xor_trace {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (positive : 1 ≤ p) (programDomain : GPowerDomain p) (memoryDomain : GPowerDomain m)
    (memories : Nat → PartialMemory m) (fragment : SetXorFragment program memories)
    (finished : Completes (memories (p - 1)) (vectorImage mem)) :
    StepTrace program mem registersAt (p - 1) := by
  have growth : ∀ i, i < p - 1 → Evolves (memories i) (memories (i + 1)) :=
    fun i hi => (fragment i hi).evolves
  apply straightline_trace program mem positive programDomain
  intro i hi
  exact (fragment i hi).simulates mem memoryDomain
    (evolves_suffix memories (p - 1) growth (i + 1) (by omega)) finished

/-- Fuel accounting shared by all straight-line fragments with a derived trace. -/
theorem run_straightline {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (fuel : Nat) (valid : ValidInstance program mem publicInput)
    (trace : StepTrace program mem registersAt (p - 1)) :
    run program mem publicInput fuel =
      ⟨registersAt (min fuel (p - 1)), if p - 1 ≤ fuel then .Halted else .OutOfFuel⟩ := by
  by_cases enough : p - 1 ≤ fuel
  · simpa [registersAt, enough, Nat.min_eq_right enough] using
      run_trace_terminal program mem publicInput fuel (p - 1) valid registersAt trace enough
  · have short : fuel < p - 1 := by omega
    simpa [enough, Nat.min_eq_left (Nat.le_of_lt short)] using
      run_trace_out_of_fuel program mem publicInput fuel (p - 1) valid registersAt trace short

/-- Exact register and fuel accounting for the SET/XOR fragment of the actual
Sail runner. It executes min(fuel, p-1) instructions, never executing the sentinel. -/
theorem run_set_xor {p m : Nat} (program : Vector instruction p) (mem : Vector Word m)
    (publicInput : BitVec 256) (fuel : Nat) (valid : ValidInstance program mem publicInput)
    (programDomain : GPowerDomain p) (memoryDomain : GPowerDomain m)
    (memories : Nat → PartialMemory m) (fragment : SetXorFragment program memories)
    (finished : Completes (memories (p - 1)) (vectorImage mem)) :
    run program mem publicInput fuel =
      ⟨registersAt (min fuel (p - 1)), if p - 1 ≤ fuel then .Halted else .OutOfFuel⟩ := by
  exact run_straightline program mem publicInput fuel valid
    (set_xor_trace program mem valid.programPositive programDomain memoryDomain
      memories fragment finished)

end Leanisa.Proofs

#print axioms Leanisa.Proofs.run_trace_terminal
#print axioms Leanisa.Proofs.run_trace_out_of_fuel
#print axioms Leanisa.Proofs.set_xor_trace
#print axioms Leanisa.Proofs.run_set_xor
#print axioms Leanisa.Proofs.run_prefix_out_of_fuel
#print axioms Leanisa.Proofs.run_prefix_terminal
#print axioms Leanisa.Proofs.run_prefix_bad_fetch
#print axioms Leanisa.Proofs.run_prefix_failed_step
#print axioms Leanisa.Proofs.run_invalid_instance
