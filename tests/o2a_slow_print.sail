$include <string.sail>

// One canonical, newline-delimited envelope.  Each field has a fixed position;
// every cell, pending pair and trace event is emitted, including diagnostics.
function o2a_origin_number(x : o2a_origin) -> int = match x {
  O2aUnknown => 0, O2aSupplied => 1, O2aPublic => 2,
  O2aSuppliedPublic => 3, O2aAdvice => 4, O2aEagerZero => 5,
  O2aOutput => 6, O2aPropagated => 7, O2aComponentDefault => 8
}

function o2a_status_number(x : o2a_status) -> int = match x {
  O2aRunning => 0, O2aGeneratedHalted => 1, O2aGeneratedPrefix => 2,
  O2aInvalidShape => 3, O2aPublicInputConflict => 4,
  O2aAdviceOutOfBounds => 5, O2aAdviceConflict => 6,
  O2aAddressOutOfBounds => 7, O2aAssignmentConflict => 8,
  O2aOperandOutsideK => 9, O2aOperandOutsideChunk => 10,
  O2aFetchFailure => 11, O2aTerminalFrame => 12,
  O2aPendingUnresolved => 13, O2aCheckerRejected => 14,
  O2aCheckerMismatch => 15, O2aEqualityConflict => 16
}

function o2a_tag_number(x : o2a_image_tag) -> int = match x {
  O2aDiagnosticPartial => 0, O2aDiagnosticComplete => 1,
  O2aCheckedPrefix => 2, O2aCheckedHalted => 3
}

function o2a_phase_number(x : o2a_phase) -> int = match x {
  O2aInputPhase => 0, O2aAdvicePhase => 1, O2aSentinelPhase => 2,
  O2aFuelPhase => 3, O2aFetchPhase => 4, O2aAddressPhase => 5,
  O2aObservePhase => 6, O2aPolicyPhase => 7, O2aAssignPhase => 8,
  O2aPendingPhase => 9, O2aCheckerPhase => 10
}

function o2a_event_number(x : o2a_event_kind) -> int = match x {
  O2aPublicBind => 0, O2aAdviceWrite => 1, O2aStepStart => 2,
  O2aAddressResolve => 3, O2aAddressReject => 4, O2aEagerWrite => 5,
  O2aObserve => 6, O2aOutputWrite => 7, O2aPendingPair => 8,
  O2aStepSuccess => 9, O2aFailure => 10, O2aInitialCell => 11,
  O2aPropagationWrite => 12
}

function o2a_opcode_number(x : o2a_opcode) -> int = match x {
  O2aNoOpcode => 0, O2aXorOpcode => 1, O2aMulOpcode => 2,
  O2aSetOpcode => 3, O2aDerefOpcode => 4, O2aJumpOpcode => 5,
  O2aBlakeOpcode => 6
}

function o2a_pending_number(x : o2a_pending_reason) -> int = match x {
  O2aNoPendingIssue => 0, O2aOneDefaulted => 1, O2aBothFixed => 2
}

function o2a_verdict_number(x : status) -> int = match x {
  Running => 0, Halted => 1, BadAccess => 2,
  BadValue => 3, BadInstance => 4, OutOfFuel => 5
}

function o2a_print_word(x : eword) -> unit = print_endline(dec_str(unsigned(x)))
function o2a_print_kword(x : kword) -> unit = print_endline(dec_str(unsigned(x)))
function o2a_print_nat(x : nat) -> unit = print_endline(dec_str(x))
function o2a_print_int(x : int) -> unit = print_endline(dec_str(x))
function o2a_print_bool(x : bool) -> unit =
  print_endline(if x then "1" else "0")

function o2a_print_pair(pair : o2a_pair) -> unit = {
  o2a_print_nat(pair.target);
  o2a_print_nat(pair.source)
}

val o2a_print_pairs : list(o2a_pair) -> unit
function o2a_print_pairs(pairs) = match pairs {
  [||] => print_endline("END_PAIRS"),
  pair :: rest => { o2a_print_pair(pair); o2a_print_pairs(rest) }
}

function o2a_print_event(event : o2a_event) -> unit = {
  o2a_print_int(o2a_event_number(event.kind));
  o2a_print_int(o2a_opcode_number(event.opcode));
  o2a_print_int(o2a_phase_number(event.phase));
  o2a_print_nat(event.step);
  o2a_print_kword(event.pc);
  o2a_print_kword(event.fp);
  o2a_print_kword(event.address);
  o2a_print_nat(event.index);
  o2a_print_nat(event.other);
  o2a_print_word(event.value);
  o2a_print_word(event.previous);
  o2a_print_int(o2a_origin_number(event.origin));
  o2a_print_bool(event.success);
  o2a_print_int(o2a_status_number(event.problem))
}

function o2a_print_cell_run(start : nat, count : nat, cell : option(eword),
  origin : o2a_origin, image : eword) -> unit = {
  print_endline("RUN");
  o2a_print_nat(start);
  o2a_print_nat(count);
  match cell {
    None() => print_endline("UNKNOWN"),
    Some(value) => {
      print_endline("FIXED");
      o2a_print_word(value)
    }
  };
  o2a_print_int(o2a_origin_number(origin));
  o2a_print_word(image)
}

val o2a_print_events : list(o2a_event) -> unit
function o2a_print_events(events) = match events {
  [||] => print_endline("END_EVENTS"),
  event :: rest => { o2a_print_event(event); o2a_print_events(rest) }
}

val o2a_print_result : forall 'm, 'm >= 2. o2a_result('m) -> unit
function o2a_print_result(result) = {
  print_endline("BEGIN_O2a_ENVELOPE");
  o2a_print_int(o2a_status_number(result.status));
  o2a_print_int(o2a_phase_number(result.phase));
  o2a_print_int(o2a_tag_number(result.image_tag));
  o2a_print_int(o2a_pending_number(result.pending_reason));
  o2a_print_nat(result.failing_index);
  o2a_print_nat(result.failing_other);
  o2a_print_nat(result.steps);
  o2a_print_kword(result.registers.pc);
  o2a_print_kword(result.registers.fp);
  match result.checker_result {
    None() => print_endline("NO_CHECKER"),
    Some(checker) => {
      print_endline("CHECKER");
      o2a_print_kword(checker.state.pc);
      o2a_print_kword(checker.state.fp);
      o2a_print_int(o2a_verdict_number(checker.verdict))
    }
  };
  let cells = result.cells;
  let origins = result.origins;
  let image = result.image;
  o2a_print_nat(length(cells));
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
      o2a_print_cell_run(run_start, run_count, run_cell, run_origin, run_image);
      run_start = i;
      run_count = 1;
      run_cell = cells[i];
      run_origin = origins[i];
      run_image = image[i]
    }
  };
  o2a_print_cell_run(run_start, run_count, run_cell, run_origin, run_image);
  print_endline("END_CELLS");
  o2a_print_pairs(result.pending);
  o2a_print_events(result.events);
  print_endline("END_O2a_ENVELOPE")
}
