// O1 bounded forward witness generation.  This is deliberately separate from
// the immutable-image checker in machine.sail.

enum o1_origin = O1Unknown | O1Supplied | O1Public | O1SuppliedPublic
  | O1Advice | O1EagerZero | O1Output

enum o1_status = O1Running | O1GeneratedHalted | O1GeneratedPrefix
  | O1InvalidShape | O1PublicInputConflict | O1AdviceOutOfBounds
  | O1AdviceConflict | O1AddressOutOfBounds | O1AssignmentConflict
  | O1OperandOutsideK | O1OperandOutsideChunk | O1FetchFailure
  | O1TerminalFrame | O1PendingUnresolved | O1CheckerRejected
  | O1CheckerMismatch

enum o1_image_tag = O1DiagnosticPartial | O1DiagnosticComplete
  | O1CheckedPrefix | O1CheckedHalted

enum o1_event_kind = O1PublicBind | O1AdviceWrite | O1StepStart
  | O1AddressResolve | O1AddressReject | O1EagerWrite | O1Observe
  | O1OutputWrite | O1PendingPair | O1StepSuccess | O1Failure
  | O1InitialCell

enum o1_opcode = O1NoOpcode | O1XorOpcode | O1MulOpcode
  | O1SetOpcode | O1DerefOpcode | O1JumpOpcode | O1BlakeOpcode

enum o1_phase = O1InputPhase | O1AdvicePhase | O1SentinelPhase
  | O1FuelPhase | O1FetchPhase | O1AddressPhase | O1ObservePhase
  | O1PolicyPhase | O1AssignPhase | O1PendingPhase | O1CheckerPhase

enum o1_pending_reason = O1NoPendingIssue | O1OneDefaulted
  | O1BothFixed

struct o1_advice = { index : cell_index, value : eword }
struct o1_pair = { target : cell_index, source : cell_index }

struct o1_input('p, 'm, 'a), 'p >= 1 & 'm >= 2 & 'a >= 0 = {
  program : vector('p, instruction),
  initial : vector('m, option(eword)),
  advice : vector('a, o1_advice),
  public_input : bits(256),
  fuel : nat
}

// A uniform event record makes the full trace serializable across backends.
// Unused fields are zero; kind and success determine which fields are live.
struct o1_event = {
  kind : o1_event_kind,
  opcode : o1_opcode,
  phase : o1_phase,
  step : nat,
  pc : kword,
  fp : kword,
  address : kword,
  index : nat,
  other : nat,
  value : eword,
  previous : eword,
  origin : o1_origin,
  success : bool,
  problem : o1_status
}

struct o1_work('m), 'm >= 2 = {
  registers : machine_state,
  cells : vector('m, option(eword)),
  origins : vector('m, o1_origin),
  pending : list(o1_pair),
  events : list(o1_event),
  current_opcode : o1_opcode,
  status : o1_status,
  phase : o1_phase,
  failing_index : nat,
  failing_other : nat,
  pending_reason : o1_pending_reason,
  steps : nat
}

struct o1_result('m), 'm >= 2 = {
  status : o1_status,
  phase : o1_phase,
  image_tag : o1_image_tag,
  checker_result : option(step_result),
  registers : machine_state,
  cells : vector('m, option(eword)),
  origins : vector('m, o1_origin),
  image : vector('m, eword),
  pending : list(o1_pair),
  events : list(o1_event),
  failing_index : nat,
  failing_other : nat,
  pending_reason : o1_pending_reason,
  steps : nat
}

struct o1_resolved('m), 'm >= 2 = {
  work : o1_work('m), offset : option(cell_index)
}

val o1_reverse_events_acc : (list(o1_event), list(o1_event)) -> list(o1_event)
function o1_reverse_events_acc(xs, acc) = match xs {
  [||] => acc,
  x :: rest => o1_reverse_events_acc(rest, x :: acc)
}

val o1_reverse_pairs_acc : (list(o1_pair), list(o1_pair)) -> list(o1_pair)
function o1_reverse_pairs_acc(xs, acc) = match xs {
  [||] => acc,
  x :: rest => o1_reverse_pairs_acc(rest, x :: acc)
}

function o1_reverse_events(xs : list(o1_event)) -> list(o1_event) =
  o1_reverse_events_acc(xs, [||])

function o1_reverse_pairs(xs : list(o1_pair)) -> list(o1_pair) =
  o1_reverse_pairs_acc(xs, [||])

val o1_event_base : forall 'm, 'm >= 2.
  (o1_work('m), o1_event_kind, o1_phase) -> o1_event
function o1_event_base(w, kind, phase) = struct {
  kind = kind, opcode = w.current_opcode, phase = phase, step = w.steps,
  pc = w.registers.pc, fp = w.registers.fp,
  address = 0x0000000000000000, index = 0, other = 0,
  value = sail_zeros(192), previous = sail_zeros(192),
  origin = O1Unknown, success = true, problem = O1Running
}

val o1_emit : forall 'm, 'm >= 2. (o1_work('m), o1_event) -> o1_work('m)
function o1_emit(w0, event) = {
  var w = w0;
  w.events = event :: w.events;
  w
}

val o1_fail : forall 'm, 'm >= 2.
  (o1_work('m), o1_status, o1_phase, nat, nat) -> o1_work('m)
function o1_fail(w0, problem, phase, index, other) = {
  if w0.status != O1Running then return w0;
  var w = w0;
  w.status = problem;
  w.phase = phase;
  w.failing_index = index;
  w.failing_other = other;
  var event = o1_event_base(w, O1Failure, phase);
  event.index = index;
  event.other = other;
  event.success = false;
  event.problem = problem;
  o1_emit(w, event)
}

val o1_resolve : forall 'm 'i, 'm >= 2 & 0 <= 'i <= 8589934592.
  (o1_work('m), vector('i, address_entry), kword) -> o1_resolved('m)
function o1_resolve(w0, index, address) = {
  if w0.status != O1Running then return struct { work = w0, offset = None() };
  var event = o1_event_base(w0, O1AddressResolve, O1AddressPhase);
  event.address = address;
  match lookup_address(index, address) {
    Some(offset) => {
      event.index = offset;
      if offset < length(w0.cells) then {
        return struct { work = o1_emit(w0, event), offset = Some(offset) }
      };
      event.kind = O1AddressReject;
      event.success = false;
      event.problem = O1AddressOutOfBounds;
      let w = o1_emit(w0, event);
      return struct {
        work = o1_fail(w, O1AddressOutOfBounds, O1AddressPhase, offset, 0),
        offset = None()
      }
    },
    None() => ()
  };
  event.kind = O1AddressReject;
  event.success = false;
  event.problem = O1AddressOutOfBounds;
  let w = o1_emit(w0, event);
  struct { work = o1_fail(w, O1AddressOutOfBounds, O1AddressPhase, 0, 0), offset = None() }
}

val o1_offset : option(cell_index) -> cell_index
function o1_offset(x) = match x { Some(i) => i, None() => 0 }

val o1_observe : forall 'm, 'm >= 2.
  (o1_work('m), cell_index) -> o1_work('m)
function o1_observe(w0, index) = {
  if w0.status != O1Running then return w0;
  if index >= length(w0.cells) then
    return o1_fail(w0, O1AddressOutOfBounds, O1AddressPhase, index, 0);
  var w = w0;
  match w.cells[index] {
    None() => {
      w.cells[index] = Some(sail_zeros(192));
      w.origins[index] = O1EagerZero;
      var fixed = o1_event_base(w, O1EagerWrite, O1ObservePhase);
      fixed.index = index;
      fixed.origin = O1EagerZero;
      w = o1_emit(w, fixed)
    },
    Some(_) => ()
  };
  var event = o1_event_base(w, O1Observe, O1ObservePhase);
  event.index = index;
  event.value = match w.cells[index] { Some(x) => x, None() => sail_zeros(192) };
  event.origin = w.origins[index];
  o1_emit(w, event)
}

val o1_value : forall 'm, 'm >= 2.
  (o1_work('m), cell_index) -> eword
function o1_value(w, index) = {
  if index < length(w.cells) then
    match w.cells[index] { Some(x) => x, None() => sail_zeros(192) }
  else sail_zeros(192)
}

val o1_assign : forall 'm, 'm >= 2.
  (o1_work('m), cell_index, eword, o1_origin, o1_status, o1_phase,
   o1_event_kind) -> o1_work('m)
function o1_assign(w0, index, value, origin, conflict, phase, kind) = {
  if w0.status != O1Running then return w0;
  if index >= length(w0.cells) then
    return o1_fail(w0, O1AddressOutOfBounds, O1AddressPhase, index, 0);
  var w = w0;
  var event = o1_event_base(w, kind, phase);
  event.index = index;
  event.value = value;
  event.origin = origin;
  match w.cells[index] {
    Some(previous) => {
      event.previous = previous;
      if previous != value then {
        event.success = false;
        event.problem = conflict;
        w = o1_emit(w, event);
        return o1_fail(w, conflict, phase, index, 0)
      }
    },
    None() => {
      w.cells[index] = Some(value);
      w.origins[index] = origin
    }
  };
  o1_emit(w, event)
}

val o1_pending : forall 'm, 'm >= 2.
  (o1_work('m), cell_index, cell_index) -> o1_work('m)
function o1_pending(w0, target, source) = {
  var w = w0;
  let pair : o1_pair = struct { target = target, source = source };
  w.pending = pair :: w.pending;
  var event = o1_event_base(w, O1PendingPair, O1PolicyPhase);
  event.index = target;
  event.other = source;
  o1_emit(w, event)
}

val o1_step : forall 'm 'i, 'm >= 2 & 0 <= 'i <= 8589934592.
  (o1_work('m), instruction, vector('i, address_entry)) -> o1_work('m)
function o1_step(w0, ins, index) = {
  var w = w0;
  w.current_opcode = match ins {
    Xor(_, _, _) => O1XorOpcode,
    Mul(_, _, _) => O1MulOpcode,
    Set(_, _) => O1SetOpcode,
    Deref(_, _, _, _) => O1DerefOpcode,
    Jump(_, _, _) => O1JumpOpcode,
    Blake2s(_, _, _, _, _, _, _) => O1BlakeOpcode
  };
  w = o1_emit(w, o1_event_base(w, O1StepStart, O1PolicyPhase));
  var next : machine_state = struct { pc = advance(w.registers.pc), fp = w.registers.fp };
  match ins {
    Set(o, value) => {
      let r = o1_resolve(w, index, kmul(w.registers.fp, o));
      w = r.work;
      if w.status != O1Running then return w;
      w = o1_assign(w, o1_offset(r.offset), value, O1Output,
        O1AssignmentConflict, O1AssignPhase, O1OutputWrite)
    },
    Xor(a, b, c) => {
      let ra = o1_resolve(w, index, kmul(w.registers.fp, a)); w = ra.work;
      let rb = o1_resolve(w, index, kmul(w.registers.fp, b)); w = rb.work;
      let rc = o1_resolve(w, index, kmul(w.registers.fp, c)); w = rc.work;
      if w.status != O1Running then return w;
      let ia = o1_offset(ra.offset); let ib = o1_offset(rb.offset);
      let ic = o1_offset(rc.offset);
      w = o1_observe(w, ia);
      w = o1_observe(w, ib);
      w = o1_assign(w, ic, o1_value(w, ia) ^^ o1_value(w, ib),
        O1Output, O1AssignmentConflict, O1AssignPhase, O1OutputWrite)
    },
    Mul(a, b, c) => {
      let ra = o1_resolve(w, index, kmul(w.registers.fp, a)); w = ra.work;
      let rb = o1_resolve(w, index, kmul(w.registers.fp, b)); w = rb.work;
      let rc = o1_resolve(w, index, kmul(w.registers.fp, c)); w = rc.work;
      if w.status != O1Running then return w;
      let ia = o1_offset(ra.offset); let ib = o1_offset(rb.offset);
      let ic = o1_offset(rc.offset);
      w = o1_observe(w, ia);
      w = o1_observe(w, ib);
      w = o1_assign(w, ic, emul(o1_value(w, ia), o1_value(w, ib)),
        O1Output, O1AssignmentConflict, O1AssignPhase, O1OutputWrite)
    },
    Jump(oc, od, ofp) => {
      let rc = o1_resolve(w, index, kmul(w.registers.fp, oc)); w = rc.work;
      let rd = o1_resolve(w, index, kmul(w.registers.fp, od)); w = rd.work;
      let rf = o1_resolve(w, index, kmul(w.registers.fp, ofp)); w = rf.work;
      if w.status != O1Running then return w;
      let ic = o1_offset(rc.offset); let id = o1_offset(rd.offset);
      let iff = o1_offset(rf.offset);
      w = o1_observe(w, ic);
      w = o1_observe(w, id);
      w = o1_observe(w, iff);
      let c = o1_value(w, ic); let d = o1_value(w, id);
      let f = o1_value(w, iff);
      if not_bool(in_k(c)) then
        return o1_fail(w, O1OperandOutsideK, O1PolicyPhase, ic, 0);
      if not_bool(in_k(d)) then
        return o1_fail(w, O1OperandOutsideK, O1PolicyPhase, id, 0);
      if not_bool(in_k(f)) then
        return o1_fail(w, O1OperandOutsideK, O1PolicyPhase, iff, 0);
      if c[63..0] != 0x0000000000000000 then
        next = struct { pc = d[63..0], fp = f[63..0] }
    },
    Deref(o1, o2, o3, mode) => {
      let rp = o1_resolve(w, index, kmul(w.registers.fp, o1)); w = rp.work;
      let rs = o1_resolve(w, index, kmul(w.registers.fp, o3)); w = rs.work;
      if w.status != O1Running then return w;
      let ip = o1_offset(rp.offset);
      w = o1_observe(w, ip);
      let pointer = o1_value(w, ip);
      let rt = o1_resolve(w, index, kmul(pointer[63..0], o2)); w = rt.work;
      if w.status != O1Running then return w;
      if not_bool(in_k(pointer)) then
        return o1_fail(w, O1OperandOutsideK, O1PolicyPhase, ip, 0);
      let it = o1_offset(rt.offset);
      match mode {
        Cell => w = o1_pending(w, it, o1_offset(rs.offset)),
        Pc => w = o1_assign(w, it, embed_k(advance(advance(w.registers.pc))),
          O1Output, O1AssignmentConflict, O1AssignPhase, O1OutputWrite),
        Fp => w = o1_assign(w, it, embed_k(w.registers.fp),
          O1Output, O1AssignmentConflict, O1AssignPhase, O1OutputWrite)
      }
    },
    Blake2s(o0, o1, o2, o3, ocv, oout, omd) => {
      let r0 = o1_resolve(w, index, kmul(w.registers.fp, o0)); w = r0.work;
      let r1 = o1_resolve(w, index, kmul(w.registers.fp, o1)); w = r1.work;
      let r2 = o1_resolve(w, index, kmul(w.registers.fp, o2)); w = r2.work;
      let r3 = o1_resolve(w, index, kmul(w.registers.fp, o3)); w = r3.work;
      let rcv0 = o1_resolve(w, index, kmul(w.registers.fp, ocv)); w = rcv0.work;
      let rcv1 = o1_resolve(w, index, advance(kmul(w.registers.fp, ocv))); w = rcv1.work;
      let rout0 = o1_resolve(w, index, kmul(w.registers.fp, oout)); w = rout0.work;
      let rout1 = o1_resolve(w, index, advance(kmul(w.registers.fp, oout))); w = rout1.work;
      let rmd = o1_resolve(w, index, kmul(w.registers.fp, omd)); w = rmd.work;
      if w.status != O1Running then return w;
      let i0 = o1_offset(r0.offset); let i1 = o1_offset(r1.offset);
      let i2 = o1_offset(r2.offset); let i3 = o1_offset(r3.offset);
      let icv0 = o1_offset(rcv0.offset); let icv1 = o1_offset(rcv1.offset);
      let io0 = o1_offset(rout0.offset); let io1 = o1_offset(rout1.offset);
      let imd = o1_offset(rmd.offset);
      w = o1_observe(w, i0); w = o1_observe(w, i1);
      w = o1_observe(w, i2); w = o1_observe(w, i3);
      w = o1_observe(w, icv0); w = o1_observe(w, icv1);
      w = o1_observe(w, imd);
      let m0 = o1_value(w, i0); let m1 = o1_value(w, i1);
      let m2 = o1_value(w, i2); let m3 = o1_value(w, i3);
      let cv0 = o1_value(w, icv0); let cv1 = o1_value(w, icv1);
      let md = o1_value(w, imd);
      if not_bool(in_chunk(m0)) then
        return o1_fail(w, O1OperandOutsideChunk, O1PolicyPhase, i0, 0);
      if not_bool(in_chunk(m1)) then
        return o1_fail(w, O1OperandOutsideChunk, O1PolicyPhase, i1, 0);
      if not_bool(in_chunk(m2)) then
        return o1_fail(w, O1OperandOutsideChunk, O1PolicyPhase, i2, 0);
      if not_bool(in_chunk(m3)) then
        return o1_fail(w, O1OperandOutsideChunk, O1PolicyPhase, i3, 0);
      if not_bool(in_chunk(cv0)) then
        return o1_fail(w, O1OperandOutsideChunk, O1PolicyPhase, icv0, 0);
      if not_bool(in_chunk(cv1)) then
        return o1_fail(w, O1OperandOutsideChunk, O1PolicyPhase, icv1, 0);
      if not_bool(in_chunk(md)) then
        return o1_fail(w, O1OperandOutsideChunk, O1PolicyPhase, imd, 0);
      let message = m3[127..0] @ m2[127..0] @ m1[127..0] @ m0[127..0];
      let cv = cv1[127..0] @ cv0[127..0];
      let compressed = blake_compress(message, cv, md[127..0]);
      w = o1_assign(w, io0, 0x0000000000000000 @ compressed[127..0],
        O1Output, O1AssignmentConflict, O1AssignPhase, O1OutputWrite);
      if w.status != O1Running then return w;
      w = o1_assign(w, io1, 0x0000000000000000 @ compressed[255..128],
        O1Output, O1AssignmentConflict, O1AssignPhase, O1OutputWrite)
    }
  };
  if w.status != O1Running then return w;
  w.registers = next;
  w = o1_emit(w, o1_event_base(w, O1StepSuccess, O1PolicyPhase));
  w.steps = w.steps + 1;
  w
}

val o1_image : forall 'm, 'm >= 2.
  vector('m, option(eword)) -> vector('m, eword)
function o1_image(cells) = {
  var image : vector('m, eword) = vector_init(length(cells), sail_zeros(192));
  foreach (i from 0 to length(cells) - 1) {
    match cells[i] { Some(value) => image[i] = value, None() => () }
  };
  image
}

val o1_first_bad_pair : forall 'm, 'm >= 2.
  (list(o1_pair), vector('m, eword)) -> option(o1_pair)
function o1_first_bad_pair(pairs, image) = match pairs {
  [||] => None(),
  pair :: rest => {
    let target = pair.target;
    let source = pair.source;
    if target < length(image) then {
      if source < length(image) then {
        if image[target] != image[source] then Some(pair)
        else o1_first_bad_pair(rest, image)
      } else Some(pair)
    } else Some(pair)
  }
}

val o1_reason_for_pair : forall 'm, 'm >= 2.
  (vector('m, option(eword)), o1_pair) -> o1_pending_reason
function o1_reason_for_pair(cells, pair) = {
  let target = pair.target;
  let source = pair.source;
  if target < length(cells) then {
    if source < length(cells) then {
      match cells[target] {
        None() => O1OneDefaulted,
        Some(_) => match cells[source] {
          None() => O1OneDefaulted, Some(_) => O1BothFixed
        }
      }
    } else O1NoPendingIssue
  } else O1NoPendingIssue
}

val o1_pack : forall 'm, 'm >= 2.
  (o1_work('m), o1_image_tag, option(step_result)) -> o1_result('m)
function o1_pack(w, tag, checker) = struct {
  status = w.status, phase = w.phase, image_tag = tag,
  checker_result = checker, registers = w.registers,
  cells = w.cells, origins = w.origins, image = o1_image(w.cells),
  pending = o1_reverse_pairs(w.pending), events = o1_reverse_events(w.events),
  failing_index = w.failing_index, failing_other = w.failing_other,
  pending_reason = w.pending_reason,
  steps = w.steps
}

val o1_complete : forall 'p 'm, 'p >= 1 & 'm >= 2.
  (o1_work('m), vector('p, instruction), bits(256), nat, status) -> o1_result('m)
function o1_complete(w0, program, public_input, fuel, expected_verdict) = {
  let image = o1_image(w0.cells);
  match o1_first_bad_pair(o1_reverse_pairs(w0.pending), image) {
    Some(pair) => {
      var w = w0;
      w.pending_reason = o1_reason_for_pair(w.cells, pair);
      w = o1_fail(w, O1PendingUnresolved, O1PendingPhase,
        pair.target, pair.source);
      return o1_pack(w, O1DiagnosticComplete, None())
    },
    None() => ()
  };
  let checked = run(program, image, public_input, fuel);
  var w = w0;
  if checked.state != w.registers then {
    w = o1_fail(w, O1CheckerMismatch, O1CheckerPhase, 0, 0);
    return o1_pack(w, O1DiagnosticComplete, Some(checked))
  };
  if checked.verdict != expected_verdict then {
    w = o1_fail(w, O1CheckerRejected, O1CheckerPhase, 0, 0);
    return o1_pack(w, O1DiagnosticComplete, Some(checked))
  };
  if expected_verdict == BadValue then {
    w = o1_fail(w, O1TerminalFrame, O1SentinelPhase, 0, 0);
    return o1_pack(w, O1DiagnosticComplete, Some(checked))
  };
  if expected_verdict == Halted then {
    w.status = O1GeneratedHalted;
    return o1_pack(w, O1CheckedHalted, Some(checked))
  };
  w.status = O1GeneratedPrefix;
  o1_pack(w, O1CheckedPrefix, Some(checked))
}

val o1_forward_run_parts : forall 'p 'm 'a, 'p >= 1 & 'm >= 2 & 'a >= 0.
  (vector('p, instruction), vector('m, option(eword)),
   vector('a, o1_advice), bits(256), nat) -> o1_result('m)
function o1_forward_run_parts(program, initial, advice, public_input, fuel) = {
  let start : machine_state = struct {
    pc = 0x0000000000000001, fp = 0x0000000000000001
  };
  var w : o1_work('m) = struct {
    registers = start, cells = initial,
    origins = vector_init(length(initial), O1Unknown),
    pending = [||], events = [||], status = O1Running,
    current_opcode = O1NoOpcode,
    phase = O1InputPhase, failing_index = 0, failing_other = 0,
    pending_reason = O1NoPendingIssue,
    steps = 0
  };
  // This guard is intentionally before reading any supplied cell or advice.
  if not_bool(power_of_two(length(program))) | not_bool(power_of_two(length(initial)))
      | length(initial) < 65536 | length(initial) > 4294967296
      | length(program) > 4294967296 then {
    w = o1_fail(w, O1InvalidShape, O1InputPhase, 0, 0);
    return o1_pack(w, O1DiagnosticPartial, None())
  };
  foreach (i from 0 to length(initial) - 1) {
    match initial[i] {
      Some(value) => {
        w.origins[i] = O1Supplied;
        var event = o1_event_base(w, O1InitialCell, O1InputPhase);
        event.index = i;
        event.value = value;
        event.origin = O1Supplied;
        w = o1_emit(w, event)
      },
      None() => ()
    }
  };
  let low : eword = 0x0000000000000000 @ public_input[127..0];
  let high : eword = 0x0000000000000000 @ public_input[255..128];
  w = o1_assign(w, 0, low, O1Public, O1PublicInputConflict,
    O1InputPhase, O1PublicBind);
  if w.status != O1Running then return o1_pack(w, O1DiagnosticPartial, None());
  if w.origins[0] == O1Supplied then w.origins[0] = O1SuppliedPublic;
  w = o1_assign(w, 1, high, O1Public, O1PublicInputConflict,
    O1InputPhase, O1PublicBind);
  if w.status != O1Running then return o1_pack(w, O1DiagnosticPartial, None());
  if w.origins[1] == O1Supplied then w.origins[1] = O1SuppliedPublic;
  foreach (i from 0 to length(advice) - 1) {
    let entry = advice[i];
    if entry.index >= length(initial) then {
      w = o1_fail(w, O1AdviceOutOfBounds, O1AdvicePhase, entry.index, i);
      return o1_pack(w, O1DiagnosticPartial, None())
    };
    w = o1_assign(w, entry.index, entry.value, O1Advice,
      O1AdviceConflict, O1AdvicePhase, O1AdviceWrite);
    if w.status != O1Running then return o1_pack(w, O1DiagnosticPartial, None())
  };
  let sentinel = gpow(get_slice_int(64, length(program) - 1, 0));
  let size = if length(initial) >= length(program) then length(initial)
    else length(program);
  let index = build_address_index(size);
  foreach (i from 0 to fuel) {
    if w.registers.pc == sentinel then {
      let verdict = if w.registers.fp == 0x0000000000000001 then Halted
        else BadValue;
      return o1_complete(w, program, public_input, fuel, verdict)
    };
    if i == fuel then
      return o1_complete(w, program, public_input, fuel, OutOfFuel);
    match fetch_indexed(program, index, w.registers.pc) {
      None() => {
        w = o1_fail(w, O1FetchFailure, O1FetchPhase, 0, 0);
        return o1_pack(w, O1DiagnosticPartial, None())
      },
      Some(ins) => {
        w = o1_step(w, ins, index);
        if w.status != O1Running then
          return o1_pack(w, O1DiagnosticPartial, None())
      }
    }
  };
  o1_complete(w, program, public_input, fuel, OutOfFuel)
}

val forward_run : forall 'p 'm 'a, 'p >= 1 & 'm >= 2 & 'a >= 0.
  o1_input('p, 'm, 'a) -> o1_result('m)
function forward_run(input) = o1_forward_run_parts(input.program,
  input.initial, input.advice, input.public_input, input.fuel)
