// O2b1 bounded explicit MUL candidates. Plans are checked before observation;
// this runner does not generate candidates or compute an inverse.
struct o2b_plan = {
  step : nat, a_value : option(eword), b_value : option(eword)
}

enum o2b_solver_status = O2bCompleted | O2bCandidatesExhausted
  | O2bMalformedPlan | O2bCandidateCap | O2bPlanListLimit | O2bInternal

struct o2b_choice = { step : nat, ordinal : nat,
  a_value : option(eword), b_value : option(eword) }

struct o2b_result('m), 'm >= 2 = {
  common : o2a_result('m), solver : o2b_solver_status,
  choices : list(o2b_choice)
}

struct o2b_root = { key : nat, fixed : bool, value : eword }
struct o2b_values = { a : option(eword), b : option(eword), c : option(eword) }
enum o2b_trial_status = O2bTrialPass | O2bTrialReject | O2bTrialInvariant

// An ordinary untouched cell has no map entry.  Its index is a virtual
// singleton identity until the accepted assignment path materializes it.
val o2b_snapshot : forall 'm, 'm >= 2.
  (o2a_work('m), nat) -> option(o2b_root)
function o2b_snapshot(w, index) = {
  if not_bool(o2s_valid(w, index)) then return None();
  if index >= length(w.cells) then return None();
  match sp_get(w.components, index) {
    None() => match w.cells[index] {
      None() => Some(struct { key = index, fixed = false,
        value = sail_zeros(192) }),
      Some(_) => None()
    },
    Some(_) => match o2s_root_of(w, index) {
      None() => None(),
      Some(root) => {
        if root.entry.fixed then match w.cells[index] {
          Some(v) => if v == root.entry.value then Some(struct {
            key = root.key, fixed = true, value = v }) else None(),
          None() => None()
        } else match w.cells[index] {
          Some(_) => None(),
          None() => Some(struct { key = root.key, fixed = false,
            value = sail_zeros(192) })
        }
      }
    }
  }
}

// Set a temporary root value in all operand/output slots sharing its identity.
val o2b_put_value : (o2b_values, o2b_root, o2b_root, o2b_root,
  nat, eword) -> option(o2b_values)
function o2b_put_value(values0, ra, rb, rc, key, value) = {
  var values = values0;
  if ra.key == key then {
    match values.a { Some(v) => if v != value then return None(),
      None() => () };
    values.a = Some(value)
  };
  if rb.key == key then {
    match values.b { Some(v) => if v != value then return None(),
      None() => () };
    values.b = Some(value)
  };
  if rc.key == key then {
    match values.c { Some(v) => if v != value then return None(),
      None() => () };
    values.c = Some(value)
  };
  Some(values)
}

val o2b_preflight : forall 'm, 'm >= 2.
  (o2a_work('m), nat, nat, nat, o2b_plan) -> o2b_trial_status
function o2b_preflight(w, ia, ib, ic, plan) = {
  let oa = o2b_snapshot(w, ia);
  let ob = o2b_snapshot(w, ib);
  let oc = o2b_snapshot(w, ic);
  match (oa, ob, oc) {
    (Some(ra), Some(rb), Some(rc)) => {
      var values : o2b_values = struct {
        a = if ra.fixed then Some(ra.value) else None(),
        b = if rb.fixed then Some(rb.value) else None(),
        c = if rc.fixed then Some(rc.value) else None()
      };
      match plan.a_value {
        None() => (),
        Some(value) => {
          if ra.fixed then return O2bTrialReject;
          match o2b_put_value(values, ra, rb, rc, ra.key, value) {
            Some(next) => values = next,
            None() => return O2bTrialReject
          }
        }
      };
      match plan.b_value {
        None() => (),
        Some(value) => {
          if rb.fixed then return O2bTrialReject;
          match o2b_put_value(values, ra, rb, rc, rb.key, value) {
            Some(next) => values = next,
            None() => return O2bTrialReject
          }
        }
      };
      if values.a == None() then match o2b_put_value(values, ra, rb, rc,
          ra.key, sail_zeros(192)) {
        Some(next) => values = next,
        None() => return O2bTrialInvariant
      };
      if values.b == None() then match o2b_put_value(values, ra, rb, rc,
          rb.key, sail_zeros(192)) {
        Some(next) => values = next,
        None() => return O2bTrialInvariant
      };
      match (values.a, values.b) {
        (Some(va), Some(vb)) => {
          let product = emul(va, vb);
          match values.c {
            Some(v) => if v == product then O2bTrialPass else O2bTrialReject,
            None() => O2bTrialPass
          }
        },
        _ => O2bTrialInvariant
      }
    },
    _ => O2bTrialInvariant
  }
}

// One tag-first pass over the original list. Empty succeeds even at zero fuel;
// a 65th nonempty tag fails before any trial, including for a future step.
enum o2b_scan_status = O2bScanOk | O2bScanLimit
struct o2b_scan_result = {
  status : o2b_scan_status, matches_reverse : list(o2b_plan),
  matching_count : nat
}

val o2b_scan_fuel : (list(o2b_plan), nat, nat, nat,
  list(o2b_plan)) -> o2b_scan_result
function o2b_scan_fuel(plans, at_step, fuel, matching_count,
  matches_reverse) = match plans {
  [||] => struct { status = O2bScanOk,
    matches_reverse = matches_reverse, matching_count = matching_count },
  plan :: rest => {
    if fuel == 0 then return struct { status = O2bScanLimit,
      matches_reverse = matches_reverse, matching_count = matching_count };
    let count : nat = if plan.step == at_step & matching_count < 9
      then matching_count + 1 else matching_count;
    let retained : list(o2b_plan) = if plan.step == at_step
      & matching_count < 8 then plan :: matches_reverse
      else matches_reverse;
    o2b_scan_fuel(rest, at_step, fuel - 1, count, retained)
  }
}
termination_measure o2b_scan_fuel(plans, at_step, fuel, matching_count,
  matches_reverse) = fuel

val o2b_reverse_plans_acc : (list(o2b_plan), list(o2b_plan)) -> list(o2b_plan)
function o2b_reverse_plans_acc(plans, acc) = match plans {
  [||] => acc,
  plan :: rest => o2b_reverse_plans_acc(rest, plan :: acc)
}

function o2b_reverse_plans(plans : list(o2b_plan)) -> list(o2b_plan) =
  o2b_reverse_plans_acc(plans, [||])

val o2b_malformed : list(o2b_plan) -> bool
function o2b_malformed(plans) = match plans {
  [||] => false,
  plan :: rest => (plan.a_value == None() & plan.b_value == None())
    | o2b_malformed(rest)
}

struct o2b_pick_result = { status : o2b_solver_status,
  selected : option(o2b_plan), ordinal : nat }

val o2b_pick : forall 'm, 'm >= 2.
  (o2a_work('m), nat, nat, nat, list(o2b_plan), nat) -> o2b_pick_result
function o2b_pick(w, ia, ib, ic, plans, ordinal) = match plans {
  [||] => struct { status = O2bCandidatesExhausted,
    selected = None(), ordinal = ordinal },
  plan :: rest => {
    match o2b_preflight(w, ia, ib, ic, plan) {
      O2bTrialPass => struct { status = O2bCompleted,
        selected = Some(plan), ordinal = ordinal },
      O2bTrialReject => o2b_pick(w, ia, ib, ic, rest, ordinal + 1),
      O2bTrialInvariant => struct { status = O2bInternal,
        selected = None(), ordinal = ordinal }
    }
  }
}

struct o2b_step_result('m), 'm >= 2 = {
  work : o2a_work('m), solver : o2b_solver_status,
  choice : option(o2b_choice)
}

val o2b_internalize : forall 'm, 'm >= 2.
  o2a_work('m) -> o2a_work('m)
function o2b_internalize(w0) = {
  var w = w0;
  w.status = O2aInternalInvariant;
  w.phase = O2aPolicyPhase;
  w
}

val o2b_step : forall 'm 'i, 'm >= 2 & 0 <= 'i <= 8589934592.
  (o2a_work('m), instruction, vector('i, address_entry),
   list(o2b_plan)) -> o2b_step_result('m)
function o2b_step(w0, ins, index, plans) = {
  match ins {
    Mul(a, b, c) => {
      var w = w0;
      w.current_opcode = O2aMulOpcode;
      w = o2a_emit(w, o2a_event_base(w, O2aStepStart, O2aPolicyPhase));
      let ra = o2a_resolve(w, index, kmul(w.registers.fp, a)); w = ra.work;
      if w.status != O2aRunning then return struct {
        work = w, solver = O2bCompleted, choice = None() };
      let rb = o2a_resolve(w, index, kmul(w.registers.fp, b)); w = rb.work;
      if w.status != O2aRunning then return struct {
        work = w, solver = O2bCompleted, choice = None() };
      let rc = o2a_resolve(w, index, kmul(w.registers.fp, c)); w = rc.work;
      if w.status != O2aRunning then return struct {
        work = w, solver = O2bCompleted, choice = None() };
      // The only original-list scan starts after all three resolutions.
      let scan = o2b_scan_fuel(plans, w.steps, 64, 0, [||]);
      if scan.status == O2bScanLimit then return struct { work = w,
        solver = O2bPlanListLimit, choice = None() };
      if scan.matching_count > 8 then return struct { work = w,
        solver = O2bCandidateCap, choice = None() };
      // Replaying the untouched O2a step preserves the full common envelope.
      if scan.matching_count == 0 then return struct { work = o2a_step(w0, ins, index),
        solver = O2bCompleted, choice = None() };
      let candidates = o2b_reverse_plans(scan.matches_reverse);
      if o2b_malformed(candidates) then return struct { work = w,
        solver = O2bMalformedPlan, choice = None() };
      let ia = o2a_offset(ra.offset);
      let ib = o2a_offset(rb.offset);
      let ic = o2a_offset(rc.offset);
      let picked = o2b_pick(w, ia, ib, ic, candidates, 0);
      match picked.selected {
        None() => struct {
          work = if picked.status == O2bInternal then o2b_internalize(w) else w,
          solver = picked.status, choice = None()
        },
        Some(plan) => {
          let chosen : o2b_choice = struct { step = w.steps,
            ordinal = picked.ordinal, a_value = plan.a_value,
            b_value = plan.b_value };
          match plan.a_value {
            Some(value) => w = o2a_assign(w, ia, value, O2bMulAdvice,
              O2aAssignmentConflict, O2aAssignPhase, O2bMulAdviceWrite),
            None() => ()
          };
          if w.status != O2aRunning then return struct { work = o2b_internalize(w),
            solver = O2bInternal, choice = None() };
          match plan.b_value {
            Some(value) => w = o2a_assign(w, ib, value, O2bMulAdvice,
              O2aAssignmentConflict, O2aAssignPhase, O2bMulAdviceWrite),
            None() => ()
          };
          if w.status != O2aRunning then return struct { work = o2b_internalize(w),
            solver = O2bInternal, choice = None() };
          w = o2a_observe(w, ia);
          w = o2a_observe(w, ib);
          if w.status != O2aRunning then return struct { work = o2b_internalize(w),
            solver = O2bInternal, choice = None() };
          w = o2a_assign(w, ic,
            emul(o2a_value(w, ia), o2a_value(w, ib)), O2aOutput,
            O2aAssignmentConflict, O2aAssignPhase, O2aOutputWrite);
          if w.status != O2aRunning then return struct { work = o2b_internalize(w),
            solver = O2bInternal, choice = None() };
          w.registers = struct { pc = advance(w.registers.pc),
            fp = w.registers.fp };
          w = o2a_emit(w, o2a_event_base(w, O2aStepSuccess, O2aPolicyPhase));
          w.steps = w.steps + 1;
          struct { work = w, solver = O2bCompleted,
            choice = Some(chosen) }
        }
      }
    },
    _ => struct { work = o2a_step(w0, ins, index),
      solver = O2bCompleted, choice = None() }
  }
}

// The runner prepends committed choices for cheap accumulation. Every exit,
// including a later diagnostic, exposes them in increasing dynamic-step order.
val o2b_reverse_choices_acc :
  (list(o2b_choice), list(o2b_choice)) -> list(o2b_choice)
function o2b_reverse_choices_acc(choices, acc) = match choices {
  [||] => acc,
  choice :: rest => o2b_reverse_choices_acc(rest, choice :: acc)
}

function o2b_reverse_choices(choices : list(o2b_choice)) -> list(o2b_choice) =
  o2b_reverse_choices_acc(choices, [||])

val o2b_wrap : forall 'm, 'm >= 2.
  (o2a_result('m), o2b_solver_status, list(o2b_choice)) -> o2b_result('m)
function o2b_wrap(common, solver, choices) = struct {
  common = common, solver = solver,
  choices = o2b_reverse_choices(choices)
}

val o2b_forward_run_parts : forall 'p 'm 'a,
  'p >= 1 & 'm >= 2 & 'a >= 0.
  (vector('p, instruction), vector('m, option(eword)),
   vector('a, o2a_advice), bits(256), nat, list(o2b_plan)) -> o2b_result('m)
function o2b_forward_run_parts(program, initial, advice, public_input,
  fuel, plans) = {
  let start : machine_state = struct {
    pc = 0x0000000000000001, fp = 0x0000000000000001
  };
  var w : o2a_work('m) = struct {
    registers = start, cells = initial,
    origins = vector_init(length(initial), O2aUnknown),
    pending = [||], events = [||], components = None(), status = O2aRunning,
    current_opcode = O2aNoOpcode,
    phase = O2aInputPhase, failing_index = 0, failing_other = 0,
    pending_reason = O2aNoPendingIssue, steps = 0
  };
  var choices : list(o2b_choice) = [||];
  if not_bool(power_of_two(length(program))) | not_bool(power_of_two(length(initial)))
      | length(initial) < 65536 | length(initial) > 4294967296
      | length(program) > 4294967296 then {
    w = o2a_fail(w, O2aInvalidShape, O2aInputPhase, 0, 0);
    return o2b_wrap(o2a_pack(w, O2aDiagnosticPartial, None()),
      O2bCompleted, choices)
  };
  foreach (i from 0 to length(initial) - 1) {
    match initial[i] {
      Some(value) => {
        w.origins[i] = O2aSupplied;
        var event = o2a_event_base(w, O2aInitialCell, O2aInputPhase);
        event.index = i;
        event.value = value;
        event.origin = O2aSupplied;
        w = o2a_emit(w, event);
        w = o2s_initial_register(w, i, value)
      },
      None() => ()
    }
  };
  let low : eword = 0x0000000000000000 @ public_input[127..0];
  let high : eword = 0x0000000000000000 @ public_input[255..128];
  w = o2a_assign(w, 0, low, O2aPublic, O2aPublicInputConflict,
    O2aInputPhase, O2aPublicBind);
  if w.status != O2aRunning then return o2b_wrap(
    o2a_pack(w, O2aDiagnosticPartial, None()), O2bCompleted, choices);
  if w.origins[0] == O2aSupplied then w.origins[0] = O2aSuppliedPublic;
  w = o2a_assign(w, 1, high, O2aPublic, O2aPublicInputConflict,
    O2aInputPhase, O2aPublicBind);
  if w.status != O2aRunning then return o2b_wrap(
    o2a_pack(w, O2aDiagnosticPartial, None()), O2bCompleted, choices);
  if w.origins[1] == O2aSupplied then w.origins[1] = O2aSuppliedPublic;
  foreach (i from 0 to length(advice) - 1) {
    let entry = advice[i];
    if entry.index >= length(initial) then {
      w = o2a_fail(w, O2aAdviceOutOfBounds, O2aAdvicePhase, entry.index, i);
      return o2b_wrap(o2a_pack(w, O2aDiagnosticPartial, None()),
        O2bCompleted, choices)
    };
    w = o2a_assign(w, entry.index, entry.value, O2aAdvice,
      O2aAdviceConflict, O2aAdvicePhase, O2aAdviceWrite);
    if w.status != O2aRunning then return o2b_wrap(
      o2a_pack(w, O2aDiagnosticPartial, None()), O2bCompleted, choices)
  };
  let sentinel = gpow(get_slice_int(64, length(program) - 1, 0));
  let size = if length(initial) >= length(program) then length(initial)
    else length(program);
  let index = build_address_index(size);
  foreach (i from 0 to fuel) {
    if w.registers.pc == sentinel then {
      let verdict = if w.registers.fp == 0x0000000000000001 then Halted
        else BadValue;
      return o2b_wrap(o2a_complete(w, program, public_input, fuel, verdict),
        O2bCompleted, choices)
    };
    if i == fuel then return o2b_wrap(o2a_complete(w, program,
      public_input, fuel, OutOfFuel), O2bCompleted, choices);
    match fetch_indexed(program, index, w.registers.pc) {
      None() => {
        w = o2a_fail(w, O2aFetchFailure, O2aFetchPhase, 0, 0);
        return o2b_wrap(o2a_pack(w, O2aDiagnosticPartial, None()),
          O2bCompleted, choices)
      },
      Some(ins) => {
        let stepped = o2b_step(w, ins, index, plans);
        w = stepped.work;
        match stepped.choice { Some(choice) => choices = choice :: choices,
          None() => () };
        if stepped.solver != O2bCompleted then return o2b_wrap(
          o2a_pack(w, O2aDiagnosticPartial, None()), stepped.solver, choices);
        if w.status != O2aRunning then return o2b_wrap(
          o2a_pack(w, O2aDiagnosticPartial, None()), O2bCompleted, choices)
      }
    }
  };
  o2b_wrap(o2a_complete(w, program, public_input, fuel, OutOfFuel),
    O2bCompleted, choices)
}
