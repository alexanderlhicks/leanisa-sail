$include <string.sail>

// One canonical, newline-delimited envelope.  Each field has a fixed position;
// every cell, pending pair and trace event is emitted, including diagnostics.
function o1_origin_number(x : o1_origin) -> int = match x {
  O1Unknown => 0, O1Supplied => 1, O1Public => 2,
  O1SuppliedPublic => 3, O1Advice => 4, O1EagerZero => 5,
  O1Output => 6
}

function o1_status_number(x : o1_status) -> int = match x {
  O1Running => 0, O1GeneratedHalted => 1, O1GeneratedPrefix => 2,
  O1InvalidShape => 3, O1PublicInputConflict => 4,
  O1AdviceOutOfBounds => 5, O1AdviceConflict => 6,
  O1AddressOutOfBounds => 7, O1AssignmentConflict => 8,
  O1OperandOutsideK => 9, O1OperandOutsideChunk => 10,
  O1FetchFailure => 11, O1TerminalFrame => 12,
  O1PendingUnresolved => 13, O1CheckerRejected => 14,
  O1CheckerMismatch => 15
}

function o1_tag_number(x : o1_image_tag) -> int = match x {
  O1DiagnosticPartial => 0, O1DiagnosticComplete => 1,
  O1CheckedPrefix => 2, O1CheckedHalted => 3
}

function o1_phase_number(x : o1_phase) -> int = match x {
  O1InputPhase => 0, O1AdvicePhase => 1, O1SentinelPhase => 2,
  O1FuelPhase => 3, O1FetchPhase => 4, O1AddressPhase => 5,
  O1ObservePhase => 6, O1PolicyPhase => 7, O1AssignPhase => 8,
  O1PendingPhase => 9, O1CheckerPhase => 10
}

function o1_event_number(x : o1_event_kind) -> int = match x {
  O1PublicBind => 0, O1AdviceWrite => 1, O1StepStart => 2,
  O1AddressResolve => 3, O1AddressReject => 4, O1EagerWrite => 5,
  O1Observe => 6, O1OutputWrite => 7, O1PendingPair => 8,
  O1StepSuccess => 9, O1Failure => 10, O1InitialCell => 11
}

function o1_opcode_number(x : o1_opcode) -> int = match x {
  O1NoOpcode => 0, O1XorOpcode => 1, O1MulOpcode => 2,
  O1SetOpcode => 3, O1DerefOpcode => 4, O1JumpOpcode => 5,
  O1BlakeOpcode => 6
}

function o1_pending_number(x : o1_pending_reason) -> int = match x {
  O1NoPendingIssue => 0, O1OneDefaulted => 1, O1BothFixed => 2
}

function o1_verdict_number(x : status) -> int = match x {
  Running => 0, Halted => 1, BadAccess => 2,
  BadValue => 3, BadInstance => 4, OutOfFuel => 5
}

function o1_print_word(x : eword) -> unit = print_endline(dec_str(unsigned(x)))
function o1_print_kword(x : kword) -> unit = print_endline(dec_str(unsigned(x)))
function o1_print_nat(x : nat) -> unit = print_endline(dec_str(x))
function o1_print_int(x : int) -> unit = print_endline(dec_str(x))
function o1_print_bool(x : bool) -> unit =
  print_endline(if x then "1" else "0")

function o1_print_pair(pair : o1_pair) -> unit = {
  o1_print_nat(pair.target);
  o1_print_nat(pair.source)
}

val o1_print_pairs : list(o1_pair) -> unit
function o1_print_pairs(pairs) = match pairs {
  [||] => print_endline("END_PAIRS"),
  pair :: rest => { o1_print_pair(pair); o1_print_pairs(rest) }
}

function o1_print_event(event : o1_event) -> unit = {
  o1_print_int(o1_event_number(event.kind));
  o1_print_int(o1_opcode_number(event.opcode));
  o1_print_int(o1_phase_number(event.phase));
  o1_print_nat(event.step);
  o1_print_kword(event.pc);
  o1_print_kword(event.fp);
  o1_print_kword(event.address);
  o1_print_nat(event.index);
  o1_print_nat(event.other);
  o1_print_word(event.value);
  o1_print_word(event.previous);
  o1_print_int(o1_origin_number(event.origin));
  o1_print_bool(event.success);
  o1_print_int(o1_status_number(event.problem))
}

function o1_print_cell_run(start : nat, count : nat, cell : option(eword),
  origin : o1_origin, image : eword) -> unit = {
  print_endline("RUN");
  o1_print_nat(start);
  o1_print_nat(count);
  match cell {
    None() => print_endline("UNKNOWN"),
    Some(value) => {
      print_endline("FIXED");
      o1_print_word(value)
    }
  };
  o1_print_int(o1_origin_number(origin));
  o1_print_word(image)
}

val o1_print_events : list(o1_event) -> unit
function o1_print_events(events) = match events {
  [||] => print_endline("END_EVENTS"),
  event :: rest => { o1_print_event(event); o1_print_events(rest) }
}

val o1_print_result : forall 'm, 'm >= 2. o1_result('m) -> unit
function o1_print_result(result) = {
  print_endline("BEGIN_O1_ENVELOPE");
  o1_print_int(o1_status_number(result.status));
  o1_print_int(o1_phase_number(result.phase));
  o1_print_int(o1_tag_number(result.image_tag));
  o1_print_int(o1_pending_number(result.pending_reason));
  o1_print_nat(result.failing_index);
  o1_print_nat(result.failing_other);
  o1_print_nat(result.steps);
  o1_print_kword(result.registers.pc);
  o1_print_kword(result.registers.fp);
  match result.checker_result {
    None() => print_endline("NO_CHECKER"),
    Some(checker) => {
      print_endline("CHECKER");
      o1_print_kword(checker.state.pc);
      o1_print_kword(checker.state.fp);
      o1_print_int(o1_verdict_number(checker.verdict))
    }
  };
  let cells = result.cells;
  let origins = result.origins;
  let image = result.image;
  o1_print_nat(length(cells));
  var run_start : nat = 0;
  var run_count : nat = 1;
  var run_cell = cells[0];
  var run_origin = origins[0];
  var run_image = image[0];
  foreach (i from 1 to length(cells) - 1) {
    if cells[i] == run_cell & origins[i] == run_origin
      & image[i] == run_image then {
      run_count = run_count + 1
    } else {
      o1_print_cell_run(run_start, run_count, run_cell, run_origin, run_image);
      run_start = i;
      run_count = 1;
      run_cell = cells[i];
      run_origin = origins[i];
      run_image = image[i]
    }
  };
  o1_print_cell_run(run_start, run_count, run_cell, run_origin, run_image);
  print_endline("END_CELLS");
  o1_print_pairs(result.pending);
  o1_print_events(result.events);
  print_endline("END_O1_ENVELOPE")
}
