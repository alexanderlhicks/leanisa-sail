// O2a bounded forward witness generation.  This is deliberately separate from
// the immutable-image checker in machine.sail.

enum o2a_origin = O2aUnknown | O2aSupplied | O2aPublic | O2aSuppliedPublic
  | O2aAdvice | O2aEagerZero | O2aOutput | O2aPropagated | O2aComponentDefault

enum o2a_status = O2aRunning | O2aGeneratedHalted | O2aGeneratedPrefix
  | O2aInvalidShape | O2aPublicInputConflict | O2aAdviceOutOfBounds
  | O2aAdviceConflict | O2aAddressOutOfBounds | O2aAssignmentConflict
  | O2aOperandOutsideK | O2aOperandOutsideChunk | O2aFetchFailure
  | O2aTerminalFrame | O2aPendingUnresolved | O2aCheckerRejected
  | O2aCheckerMismatch | O2aEqualityConflict

enum o2a_image_tag = O2aDiagnosticPartial | O2aDiagnosticComplete
  | O2aCheckedPrefix | O2aCheckedHalted

enum o2a_event_kind = O2aPublicBind | O2aAdviceWrite | O2aStepStart
  | O2aAddressResolve | O2aAddressReject | O2aEagerWrite | O2aObserve
  | O2aOutputWrite | O2aPendingPair | O2aStepSuccess | O2aFailure
  | O2aInitialCell | O2aPropagationWrite

enum o2a_opcode = O2aNoOpcode | O2aXorOpcode | O2aMulOpcode
  | O2aSetOpcode | O2aDerefOpcode | O2aJumpOpcode | O2aBlakeOpcode

enum o2a_phase = O2aInputPhase | O2aAdvicePhase | O2aSentinelPhase
  | O2aFuelPhase | O2aFetchPhase | O2aAddressPhase | O2aObservePhase
  | O2aPolicyPhase | O2aAssignPhase | O2aPendingPhase | O2aCheckerPhase

enum o2a_pending_reason = O2aNoPendingIssue | O2aOneDefaulted
  | O2aBothFixed

struct o2a_advice = { index : cell_index, value : eword }
struct o2a_pair = { target : cell_index, source : cell_index }

struct o2a_input('p, 'm, 'a), 'p >= 1 & 'm >= 2 & 'a >= 0 = {
  program : vector('p, instruction),
  initial : vector('m, option(eword)),
  advice : vector('a, o2a_advice),
  public_input : bits(256),
  fuel : nat
}

// A uniform event record makes the full trace serializable across backends.
// Unused fields are zero; kind and success determine which fields are live.
struct o2a_event = {
  kind : o2a_event_kind,
  opcode : o2a_opcode,
  phase : o2a_phase,
  step : nat,
  pc : kword,
  fp : kword,
  address : kword,
  index : nat,
  other : nat,
  value : eword,
  previous : eword,
  origin : o2a_origin,
  success : bool,
  problem : o2a_status
}

struct o2a_work('m), 'm >= 2 = {
  registers : machine_state,
  cells : vector('m, option(eword)),
  origins : vector('m, o2a_origin),
  pending : list(o2a_pair),
  events : list(o2a_event),
  current_opcode : o2a_opcode,
  status : o2a_status,
  phase : o2a_phase,
  failing_index : nat,
  failing_other : nat,
  pending_reason : o2a_pending_reason,
  steps : nat
}

struct o2a_result('m), 'm >= 2 = {
  status : o2a_status,
  phase : o2a_phase,
  image_tag : o2a_image_tag,
  checker_result : option(step_result),
  registers : machine_state,
  cells : vector('m, option(eword)),
  origins : vector('m, o2a_origin),
  image : vector('m, eword),
  pending : list(o2a_pair),
  events : list(o2a_event),
  failing_index : nat,
  failing_other : nat,
  pending_reason : o2a_pending_reason,
  steps : nat
}

struct o2a_resolved('m), 'm >= 2 = {
  work : o2a_work('m), offset : option(cell_index)
}

val o2a_reverse_events_acc : (list(o2a_event), list(o2a_event)) -> list(o2a_event)
function o2a_reverse_events_acc(xs, acc) = match xs {
  [||] => acc,
  x :: rest => o2a_reverse_events_acc(rest, x :: acc)
}

val o2a_reverse_pairs_acc : (list(o2a_pair), list(o2a_pair)) -> list(o2a_pair)
function o2a_reverse_pairs_acc(xs, acc) = match xs {
  [||] => acc,
  x :: rest => o2a_reverse_pairs_acc(rest, x :: acc)
}

function o2a_reverse_events(xs : list(o2a_event)) -> list(o2a_event) =
  o2a_reverse_events_acc(xs, [||])

function o2a_reverse_pairs(xs : list(o2a_pair)) -> list(o2a_pair) =
  o2a_reverse_pairs_acc(xs, [||])

val o2a_event_base : forall 'm, 'm >= 2.
  (o2a_work('m), o2a_event_kind, o2a_phase) -> o2a_event
function o2a_event_base(w, kind, phase) = struct {
  kind = kind, opcode = w.current_opcode, phase = phase, step = w.steps,
  pc = w.registers.pc, fp = w.registers.fp,
  address = 0x0000000000000000, index = 0, other = 0,
  value = sail_zeros(192), previous = sail_zeros(192),
  origin = O2aUnknown, success = true, problem = O2aRunning
}

val o2a_emit : forall 'm, 'm >= 2. (o2a_work('m), o2a_event) -> o2a_work('m)
function o2a_emit(w0, event) = {
  var w = w0;
  w.events = event :: w.events;
  w
}

val o2a_fail : forall 'm, 'm >= 2.
  (o2a_work('m), o2a_status, o2a_phase, nat, nat) -> o2a_work('m)
function o2a_fail(w0, problem, phase, index, other) = {
  if w0.status != O2aRunning then return w0;
  var w = w0;
  w.status = problem;
  w.phase = phase;
  w.failing_index = index;
  w.failing_other = other;
  var event = o2a_event_base(w, O2aFailure, phase);
  event.index = index;
  event.other = other;
  event.success = false;
  event.problem = problem;
  o2a_emit(w, event)
}

val o2a_resolve : forall 'm 'i, 'm >= 2 & 0 <= 'i <= 8589934592.
  (o2a_work('m), vector('i, address_entry), kword) -> o2a_resolved('m)
function o2a_resolve(w0, index, address) = {
  if w0.status != O2aRunning then return struct { work = w0, offset = None() };
  var event = o2a_event_base(w0, O2aAddressResolve, O2aAddressPhase);
  event.address = address;
  match lookup_address(index, address) {
    Some(offset) => {
      event.index = offset;
      if offset < length(w0.cells) then {
        return struct { work = o2a_emit(w0, event), offset = Some(offset) }
      };
      event.kind = O2aAddressReject;
      event.success = false;
      event.problem = O2aAddressOutOfBounds;
      let w = o2a_emit(w0, event);
      return struct {
        work = o2a_fail(w, O2aAddressOutOfBounds, O2aAddressPhase, offset, 0),
        offset = None()
      }
    },
    None() => ()
  };
  event.kind = O2aAddressReject;
  event.success = false;
  event.problem = O2aAddressOutOfBounds;
  let w = o2a_emit(w0, event);
  struct { work = o2a_fail(w, O2aAddressOutOfBounds, O2aAddressPhase, 0, 0), offset = None() }
}

val o2a_offset : option(cell_index) -> cell_index
function o2a_offset(x) = match x { Some(i) => i, None() => 0 }

// Slow reference control: close one connected component by
// repeated passes over the original ordered pair list.  A production O2a
// needs a sparse component table; this implementation has O(m + q^2) work
// per propagation where m is memory size and q is the number of pairs.
val o2a_mark_pass : forall 'm, 'm >= 2.
  (list(o2a_pair), vector('m, bool)) -> vector('m, bool)
function o2a_mark_pass(pairs, marks0) = match pairs {
  [||] => marks0,
  pair :: rest => {
    var marks = marks0;
    let target = pair.target;
    let source = pair.source;
    if target < length(marks) then {
      if source < length(marks) then {
        if marks[target] | marks[source] then {
          marks[target] = true;
          marks[source] = true
        }
      }
    };
    o2a_mark_pass(rest, marks)
  }
}

val o2a_pair_count : list(o2a_pair) -> nat
function o2a_pair_count(pairs) = match pairs {
  [||] => 0,
  _ :: rest => 1 + o2a_pair_count(rest)
}

val o2a_propagate : forall 'm, 'm >= 2.
  (o2a_work('m), cell_index, bool) -> o2a_work('m)
function o2a_propagate(w0, index, terminal) = {
  if w0.status != O2aRunning then return w0;
  if index >= length(w0.cells) then
    return o2a_fail(w0, O2aAddressOutOfBounds, O2aAddressPhase, index, 0);
  var marks : vector('m, bool) = vector_init(length(w0.cells), false);
  marks[index] = true;
  foreach (round from 0 to o2a_pair_count(w0.pending)) {
    marks = o2a_mark_pass(w0.pending, marks)
  };
  var known : option(eword) = None();
  var known_index : nat = 0;
  foreach (i from 0 to length(w0.cells) - 1) {
    if marks[i] then {
      match w0.cells[i] {
        None() => (),
        Some(value) => match known {
          None() => { known = Some(value); known_index = i },
          Some(first) => if value != first then
            return o2a_fail(w0, O2aEqualityConflict, O2aPendingPhase,
              known_index, i)
        }
      }
    }
  };
  if known == None() & terminal then known = Some(sail_zeros(192));
  var w = w0;
  match known {
    None() => (),
    Some(value) => {
      foreach (i from 0 to length(w.cells) - 1) {
        if marks[i] then {
          match w.cells[i] {
            Some(_) => (),
            None() => {
              w.cells[i] = Some(value);
              w.origins[i] = if terminal then O2aComponentDefault
                else O2aPropagated;
              var event = o2a_event_base(w, O2aPropagationWrite,
                O2aPendingPhase);
              event.index = i;
              event.value = value;
              event.origin = w.origins[i];
              w = o2a_emit(w, event)
            }
          }
        }
      }
    }
  };
  w
}

val o2a_observe : forall 'm, 'm >= 2.
  (o2a_work('m), cell_index) -> o2a_work('m)
function o2a_observe(w0, index) = {
  let w0 = o2a_propagate(w0, index, false);
  if w0.status != O2aRunning then return w0;
  if index >= length(w0.cells) then
    return o2a_fail(w0, O2aAddressOutOfBounds, O2aAddressPhase, index, 0);
  var w = w0;
  match w.cells[index] {
    None() => {
      w.cells[index] = Some(sail_zeros(192));
      w.origins[index] = O2aEagerZero;
      var fixed = o2a_event_base(w, O2aEagerWrite, O2aObservePhase);
      fixed.index = index;
      fixed.origin = O2aEagerZero;
      w = o2a_emit(w, fixed)
    },
    Some(_) => ()
  };
  var event = o2a_event_base(w, O2aObserve, O2aObservePhase);
  event.index = index;
  event.value = match w.cells[index] { Some(x) => x, None() => sail_zeros(192) };
  event.origin = w.origins[index];
  o2a_propagate(o2a_emit(w, event), index, false)
}

val o2a_value : forall 'm, 'm >= 2.
  (o2a_work('m), cell_index) -> eword
function o2a_value(w, index) = {
  if index < length(w.cells) then
    match w.cells[index] { Some(x) => x, None() => sail_zeros(192) }
  else sail_zeros(192)
}

val o2a_assign : forall 'm, 'm >= 2.
  (o2a_work('m), cell_index, eword, o2a_origin, o2a_status, o2a_phase,
   o2a_event_kind) -> o2a_work('m)
function o2a_assign(w0, index, value, origin, conflict, phase, kind) = {
  if w0.status != O2aRunning then return w0;
  if index >= length(w0.cells) then
    return o2a_fail(w0, O2aAddressOutOfBounds, O2aAddressPhase, index, 0);
  var w = w0;
  var event = o2a_event_base(w, kind, phase);
  event.index = index;
  event.value = value;
  event.origin = origin;
  match w.cells[index] {
    Some(previous) => {
      event.previous = previous;
      if previous != value then {
        event.success = false;
        event.problem = conflict;
        w = o2a_emit(w, event);
        return o2a_fail(w, conflict, phase, index, 0)
      }
    },
    None() => {
      w.cells[index] = Some(value);
      w.origins[index] = origin
    }
  };
  o2a_propagate(o2a_emit(w, event), index, false)
}

val o2a_pending : forall 'm, 'm >= 2.
  (o2a_work('m), cell_index, cell_index) -> o2a_work('m)
function o2a_pending(w0, target, source) = {
  var w = w0;
  let pair : o2a_pair = struct { target = target, source = source };
  w.pending = pair :: w.pending;
  var event = o2a_event_base(w, O2aPendingPair, O2aPolicyPhase);
  event.index = target;
  event.other = source;
  o2a_propagate(o2a_emit(w, event), target, false)
}

val o2a_step : forall 'm 'i, 'm >= 2 & 0 <= 'i <= 8589934592.
  (o2a_work('m), instruction, vector('i, address_entry)) -> o2a_work('m)
function o2a_step(w0, ins, index) = {
  var w = w0;
  w.current_opcode = match ins {
    Xor(_, _, _) => O2aXorOpcode,
    Mul(_, _, _) => O2aMulOpcode,
    Set(_, _) => O2aSetOpcode,
    Deref(_, _, _, _) => O2aDerefOpcode,
    Jump(_, _, _) => O2aJumpOpcode,
    Blake2s(_, _, _, _, _, _, _) => O2aBlakeOpcode
  };
  w = o2a_emit(w, o2a_event_base(w, O2aStepStart, O2aPolicyPhase));
  var next : machine_state = struct { pc = advance(w.registers.pc), fp = w.registers.fp };
  match ins {
    Set(o, value) => {
      let r = o2a_resolve(w, index, kmul(w.registers.fp, o));
      w = r.work;
      if w.status != O2aRunning then return w;
      w = o2a_assign(w, o2a_offset(r.offset), value, O2aOutput,
        O2aAssignmentConflict, O2aAssignPhase, O2aOutputWrite)
    },
    Xor(a, b, c) => {
      let ra = o2a_resolve(w, index, kmul(w.registers.fp, a)); w = ra.work;
      let rb = o2a_resolve(w, index, kmul(w.registers.fp, b)); w = rb.work;
      let rc = o2a_resolve(w, index, kmul(w.registers.fp, c)); w = rc.work;
      if w.status != O2aRunning then return w;
      let ia = o2a_offset(ra.offset); let ib = o2a_offset(rb.offset);
      let ic = o2a_offset(rc.offset);
      w = o2a_observe(w, ia);
      w = o2a_observe(w, ib);
      w = o2a_assign(w, ic, o2a_value(w, ia) ^^ o2a_value(w, ib),
        O2aOutput, O2aAssignmentConflict, O2aAssignPhase, O2aOutputWrite)
    },
    Mul(a, b, c) => {
      let ra = o2a_resolve(w, index, kmul(w.registers.fp, a)); w = ra.work;
      let rb = o2a_resolve(w, index, kmul(w.registers.fp, b)); w = rb.work;
      let rc = o2a_resolve(w, index, kmul(w.registers.fp, c)); w = rc.work;
      if w.status != O2aRunning then return w;
      let ia = o2a_offset(ra.offset); let ib = o2a_offset(rb.offset);
      let ic = o2a_offset(rc.offset);
      w = o2a_observe(w, ia);
      w = o2a_observe(w, ib);
      w = o2a_assign(w, ic, emul(o2a_value(w, ia), o2a_value(w, ib)),
        O2aOutput, O2aAssignmentConflict, O2aAssignPhase, O2aOutputWrite)
    },
    Jump(oc, od, ofp) => {
      let rc = o2a_resolve(w, index, kmul(w.registers.fp, oc)); w = rc.work;
      let rd = o2a_resolve(w, index, kmul(w.registers.fp, od)); w = rd.work;
      let rf = o2a_resolve(w, index, kmul(w.registers.fp, ofp)); w = rf.work;
      if w.status != O2aRunning then return w;
      let ic = o2a_offset(rc.offset); let id = o2a_offset(rd.offset);
      let iff = o2a_offset(rf.offset);
      w = o2a_observe(w, ic);
      w = o2a_observe(w, id);
      w = o2a_observe(w, iff);
      let c = o2a_value(w, ic); let d = o2a_value(w, id);
      let f = o2a_value(w, iff);
      if not_bool(in_k(c)) then
        return o2a_fail(w, O2aOperandOutsideK, O2aPolicyPhase, ic, 0);
      if not_bool(in_k(d)) then
        return o2a_fail(w, O2aOperandOutsideK, O2aPolicyPhase, id, 0);
      if not_bool(in_k(f)) then
        return o2a_fail(w, O2aOperandOutsideK, O2aPolicyPhase, iff, 0);
      if c[63..0] != 0x0000000000000000 then
        next = struct { pc = d[63..0], fp = f[63..0] }
    },
    Deref(o1, o2, o3, mode) => {
      let rp = o2a_resolve(w, index, kmul(w.registers.fp, o1)); w = rp.work;
      let rs = o2a_resolve(w, index, kmul(w.registers.fp, o3)); w = rs.work;
      if w.status != O2aRunning then return w;
      let ip = o2a_offset(rp.offset);
      w = o2a_observe(w, ip);
      let pointer = o2a_value(w, ip);
      let rt = o2a_resolve(w, index, kmul(pointer[63..0], o2)); w = rt.work;
      if w.status != O2aRunning then return w;
      if not_bool(in_k(pointer)) then
        return o2a_fail(w, O2aOperandOutsideK, O2aPolicyPhase, ip, 0);
      let it = o2a_offset(rt.offset);
      match mode {
        Cell => w = o2a_pending(w, it, o2a_offset(rs.offset)),
        Pc => w = o2a_assign(w, it, embed_k(advance(advance(w.registers.pc))),
          O2aOutput, O2aAssignmentConflict, O2aAssignPhase, O2aOutputWrite),
        Fp => w = o2a_assign(w, it, embed_k(w.registers.fp),
          O2aOutput, O2aAssignmentConflict, O2aAssignPhase, O2aOutputWrite)
      }
    },
    Blake2s(o0, o1, o2, o3, ocv, oout, omd) => {
      let r0 = o2a_resolve(w, index, kmul(w.registers.fp, o0)); w = r0.work;
      let r1 = o2a_resolve(w, index, kmul(w.registers.fp, o1)); w = r1.work;
      let r2 = o2a_resolve(w, index, kmul(w.registers.fp, o2)); w = r2.work;
      let r3 = o2a_resolve(w, index, kmul(w.registers.fp, o3)); w = r3.work;
      let rcv0 = o2a_resolve(w, index, kmul(w.registers.fp, ocv)); w = rcv0.work;
      let rcv1 = o2a_resolve(w, index, advance(kmul(w.registers.fp, ocv))); w = rcv1.work;
      let rout0 = o2a_resolve(w, index, kmul(w.registers.fp, oout)); w = rout0.work;
      let rout1 = o2a_resolve(w, index, advance(kmul(w.registers.fp, oout))); w = rout1.work;
      let rmd = o2a_resolve(w, index, kmul(w.registers.fp, omd)); w = rmd.work;
      if w.status != O2aRunning then return w;
      let i0 = o2a_offset(r0.offset); let i1 = o2a_offset(r1.offset);
      let i2 = o2a_offset(r2.offset); let i3 = o2a_offset(r3.offset);
      let icv0 = o2a_offset(rcv0.offset); let icv1 = o2a_offset(rcv1.offset);
      let io0 = o2a_offset(rout0.offset); let io1 = o2a_offset(rout1.offset);
      let imd = o2a_offset(rmd.offset);
      w = o2a_observe(w, i0); w = o2a_observe(w, i1);
      w = o2a_observe(w, i2); w = o2a_observe(w, i3);
      w = o2a_observe(w, icv0); w = o2a_observe(w, icv1);
      w = o2a_observe(w, imd);
      let m0 = o2a_value(w, i0); let m1 = o2a_value(w, i1);
      let m2 = o2a_value(w, i2); let m3 = o2a_value(w, i3);
      let cv0 = o2a_value(w, icv0); let cv1 = o2a_value(w, icv1);
      let md = o2a_value(w, imd);
      if not_bool(in_chunk(m0)) then
        return o2a_fail(w, O2aOperandOutsideChunk, O2aPolicyPhase, i0, 0);
      if not_bool(in_chunk(m1)) then
        return o2a_fail(w, O2aOperandOutsideChunk, O2aPolicyPhase, i1, 0);
      if not_bool(in_chunk(m2)) then
        return o2a_fail(w, O2aOperandOutsideChunk, O2aPolicyPhase, i2, 0);
      if not_bool(in_chunk(m3)) then
        return o2a_fail(w, O2aOperandOutsideChunk, O2aPolicyPhase, i3, 0);
      if not_bool(in_chunk(cv0)) then
        return o2a_fail(w, O2aOperandOutsideChunk, O2aPolicyPhase, icv0, 0);
      if not_bool(in_chunk(cv1)) then
        return o2a_fail(w, O2aOperandOutsideChunk, O2aPolicyPhase, icv1, 0);
      if not_bool(in_chunk(md)) then
        return o2a_fail(w, O2aOperandOutsideChunk, O2aPolicyPhase, imd, 0);
      let message = m3[127..0] @ m2[127..0] @ m1[127..0] @ m0[127..0];
      let cv = cv1[127..0] @ cv0[127..0];
      let compressed = blake_compress(message, cv, md[127..0]);
      w = o2a_assign(w, io0, 0x0000000000000000 @ compressed[127..0],
        O2aOutput, O2aAssignmentConflict, O2aAssignPhase, O2aOutputWrite);
      if w.status != O2aRunning then return w;
      w = o2a_assign(w, io1, 0x0000000000000000 @ compressed[255..128],
        O2aOutput, O2aAssignmentConflict, O2aAssignPhase, O2aOutputWrite)
    }
  };
  if w.status != O2aRunning then return w;
  w.registers = next;
  w = o2a_emit(w, o2a_event_base(w, O2aStepSuccess, O2aPolicyPhase));
  w.steps = w.steps + 1;
  w
}

val o2a_image : forall 'm, 'm >= 2.
  vector('m, option(eword)) -> vector('m, eword)
function o2a_image(cells) = {
  var image : vector('m, eword) = vector_init(length(cells), sail_zeros(192));
  foreach (i from 0 to length(cells) - 1) {
    match cells[i] { Some(value) => image[i] = value, None() => () }
  };
  image
}

val o2a_first_bad_pair : forall 'm, 'm >= 2.
  (list(o2a_pair), vector('m, eword)) -> option(o2a_pair)
function o2a_first_bad_pair(pairs, image) = match pairs {
  [||] => None(),
  pair :: rest => {
    let target = pair.target;
    let source = pair.source;
    if target < length(image) then {
      if source < length(image) then {
        if image[target] != image[source] then Some(pair)
        else o2a_first_bad_pair(rest, image)
      } else Some(pair)
    } else Some(pair)
  }
}

val o2a_reason_for_pair : forall 'm, 'm >= 2.
  (vector('m, option(eword)), o2a_pair) -> o2a_pending_reason
function o2a_reason_for_pair(cells, pair) = {
  let target = pair.target;
  let source = pair.source;
  if target < length(cells) then {
    if source < length(cells) then {
      match cells[target] {
        None() => O2aOneDefaulted,
        Some(_) => match cells[source] {
          None() => O2aOneDefaulted, Some(_) => O2aBothFixed
        }
      }
    } else O2aNoPendingIssue
  } else O2aNoPendingIssue
}

val o2a_pack : forall 'm, 'm >= 2.
  (o2a_work('m), o2a_image_tag, option(step_result)) -> o2a_result('m)
function o2a_pack(w, tag, checker) = struct {
  status = w.status, phase = w.phase, image_tag = tag,
  checker_result = checker, registers = w.registers,
  cells = w.cells, origins = w.origins, image = o2a_image(w.cells),
  pending = o2a_reverse_pairs(w.pending), events = o2a_reverse_events(w.events),
  failing_index = w.failing_index, failing_other = w.failing_other,
  pending_reason = w.pending_reason,
  steps = w.steps
}

val o2a_finalize_pairs : forall 'm, 'm >= 2.
  (o2a_work('m), list(o2a_pair)) -> o2a_work('m)
function o2a_finalize_pairs(w, pairs) = match pairs {
  [||] => w,
  pair :: rest => o2a_finalize_pairs(
    o2a_propagate(w, pair.target, true), rest)
}

val o2a_complete : forall 'p 'm, 'p >= 1 & 'm >= 2.
  (o2a_work('m), vector('p, instruction), bits(256), nat, status) -> o2a_result('m)
function o2a_complete(w0, program, public_input, fuel, expected_verdict) = {
  let w0 = o2a_finalize_pairs(w0, o2a_reverse_pairs(w0.pending));
  if w0.status != O2aRunning then
    return o2a_pack(w0, O2aDiagnosticComplete, None());
  let image = o2a_image(w0.cells);
  match o2a_first_bad_pair(o2a_reverse_pairs(w0.pending), image) {
    Some(pair) => {
      var w = w0;
      w.pending_reason = o2a_reason_for_pair(w.cells, pair);
      w = o2a_fail(w, O2aPendingUnresolved, O2aPendingPhase,
        pair.target, pair.source);
      return o2a_pack(w, O2aDiagnosticComplete, None())
    },
    None() => ()
  };
  let checked = run(program, image, public_input, fuel);
  var w = w0;
  if checked.state != w.registers then {
    w = o2a_fail(w, O2aCheckerMismatch, O2aCheckerPhase, 0, 0);
    return o2a_pack(w, O2aDiagnosticComplete, Some(checked))
  };
  if checked.verdict != expected_verdict then {
    w = o2a_fail(w, O2aCheckerRejected, O2aCheckerPhase, 0, 0);
    return o2a_pack(w, O2aDiagnosticComplete, Some(checked))
  };
  if expected_verdict == BadValue then {
    w = o2a_fail(w, O2aTerminalFrame, O2aSentinelPhase, 0, 0);
    return o2a_pack(w, O2aDiagnosticComplete, Some(checked))
  };
  if expected_verdict == Halted then {
    w.status = O2aGeneratedHalted;
    return o2a_pack(w, O2aCheckedHalted, Some(checked))
  };
  w.status = O2aGeneratedPrefix;
  o2a_pack(w, O2aCheckedPrefix, Some(checked))
}

val o2a_forward_run_parts : forall 'p 'm 'a, 'p >= 1 & 'm >= 2 & 'a >= 0.
  (vector('p, instruction), vector('m, option(eword)),
   vector('a, o2a_advice), bits(256), nat) -> o2a_result('m)
function o2a_forward_run_parts(program, initial, advice, public_input, fuel) = {
  let start : machine_state = struct {
    pc = 0x0000000000000001, fp = 0x0000000000000001
  };
  var w : o2a_work('m) = struct {
    registers = start, cells = initial,
    origins = vector_init(length(initial), O2aUnknown),
    pending = [||], events = [||], status = O2aRunning,
    current_opcode = O2aNoOpcode,
    phase = O2aInputPhase, failing_index = 0, failing_other = 0,
    pending_reason = O2aNoPendingIssue,
    steps = 0
  };
  // This guard is intentionally before reading any supplied cell or advice.
  if not_bool(power_of_two(length(program))) | not_bool(power_of_two(length(initial)))
      | length(initial) < 65536 | length(initial) > 4294967296
      | length(program) > 4294967296 then {
    w = o2a_fail(w, O2aInvalidShape, O2aInputPhase, 0, 0);
    return o2a_pack(w, O2aDiagnosticPartial, None())
  };
  foreach (i from 0 to length(initial) - 1) {
    match initial[i] {
      Some(value) => {
        w.origins[i] = O2aSupplied;
        var event = o2a_event_base(w, O2aInitialCell, O2aInputPhase);
        event.index = i;
        event.value = value;
        event.origin = O2aSupplied;
        w = o2a_emit(w, event)
      },
      None() => ()
    }
  };
  let low : eword = 0x0000000000000000 @ public_input[127..0];
  let high : eword = 0x0000000000000000 @ public_input[255..128];
  w = o2a_assign(w, 0, low, O2aPublic, O2aPublicInputConflict,
    O2aInputPhase, O2aPublicBind);
  if w.status != O2aRunning then return o2a_pack(w, O2aDiagnosticPartial, None());
  if w.origins[0] == O2aSupplied then w.origins[0] = O2aSuppliedPublic;
  w = o2a_assign(w, 1, high, O2aPublic, O2aPublicInputConflict,
    O2aInputPhase, O2aPublicBind);
  if w.status != O2aRunning then return o2a_pack(w, O2aDiagnosticPartial, None());
  if w.origins[1] == O2aSupplied then w.origins[1] = O2aSuppliedPublic;
  foreach (i from 0 to length(advice) - 1) {
    let entry = advice[i];
    if entry.index >= length(initial) then {
      w = o2a_fail(w, O2aAdviceOutOfBounds, O2aAdvicePhase, entry.index, i);
      return o2a_pack(w, O2aDiagnosticPartial, None())
    };
    w = o2a_assign(w, entry.index, entry.value, O2aAdvice,
      O2aAdviceConflict, O2aAdvicePhase, O2aAdviceWrite);
    if w.status != O2aRunning then return o2a_pack(w, O2aDiagnosticPartial, None())
  };
  let sentinel = gpow(get_slice_int(64, length(program) - 1, 0));
  let size = if length(initial) >= length(program) then length(initial)
    else length(program);
  let index = build_address_index(size);
  foreach (i from 0 to fuel) {
    if w.registers.pc == sentinel then {
      let verdict = if w.registers.fp == 0x0000000000000001 then Halted
        else BadValue;
      return o2a_complete(w, program, public_input, fuel, verdict)
    };
    if i == fuel then
      return o2a_complete(w, program, public_input, fuel, OutOfFuel);
    match fetch_indexed(program, index, w.registers.pc) {
      None() => {
        w = o2a_fail(w, O2aFetchFailure, O2aFetchPhase, 0, 0);
        return o2a_pack(w, O2aDiagnosticPartial, None())
      },
      Some(ins) => {
        w = o2a_step(w, ins, index);
        if w.status != O2aRunning then
          return o2a_pack(w, O2aDiagnosticPartial, None())
      }
    }
  };
  o2a_complete(w, program, public_input, fuel, OutOfFuel)
}

val o2a_forward_run : forall 'p 'm 'a, 'p >= 1 & 'm >= 2 & 'a >= 0.
  o2a_input('p, 'm, 'a) -> o2a_result('m)
function o2a_forward_run(input) = o2a_forward_run_parts(input.program,
  input.initial, input.advice, input.public_input, input.fuel)
