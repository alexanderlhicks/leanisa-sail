$include <string.sail>

// Deliberately wrong expected verdict after a real candidate step. This is a
// direct completion control, not a reachable nominal runner outcome.
function main() -> unit = {
  let two = embed_k(0x0000000000000002);
  let three = embed_k(0x0000000000000003);
  let mul = Mul(gpow(0x0000000000000003),
    gpow(0x0000000000000004), gpow(0x0000000000000005));
  var program : vector(2, instruction) = vector_init(2,
    Set(gpow(0x0000000000000008), sail_zeros(192)));
  program[0] = mul;
  let start : machine_state = struct {
    pc = 0x0000000000000001, fp = 0x0000000000000001
  };
  let initial : o2a_work(65536) = struct {
    registers = start,
    cells = vector_init(65536, None()),
    origins = vector_init(65536, O2aUnknown),
    pending = [||], events = [||], components = None(),
    current_opcode = O2aNoOpcode, status = O2aRunning,
    phase = O2aInputPhase, failing_index = 0, failing_other = 0,
    pending_reason = O2aNoPendingIssue, steps = 0
  };
  let plan : o2b_plan = struct {
    step = 0, a_value = Some(two), b_value = Some(three)
  };
  let stepped = o2b_step(initial, mul, build_address_index(65536),
    [|plan|]);
  let committed : bool = match stepped.choice {
    Some(choice) => choice.step == 0 & choice.ordinal == 0 &
      choice.a_value == Some(two) & choice.b_value == Some(three),
    None() => false
  };
  assert(stepped.solver == O2bCompleted & committed &
    stepped.work.cells[5] == Some(embed_k(0x0000000000000006)) &
    stepped.work.steps == 1, "CHECKER_CONTROL_COMMITTED_MUL");
  let completed = o2a_complete(stepped.work, program, sail_zeros(256),
    1, OutOfFuel);
  let checker_rejected : bool = match completed.checker_result {
    Some(checked) => checked.verdict == Halted &
      checked.state == stepped.work.registers,
    None() => false
  };
  assert(completed.status == O2aCheckerRejected &
    completed.image_tag == O2aDiagnosticComplete & checker_rejected,
    "CHECKER_CONTROL_REJECTED_WRONG_EXPECTATION");
  let visible : o2b_choice = struct {
    step = 0, ordinal = 0, a_value = Some(two), b_value = Some(three)
  };
  print_endline("SYNTHETIC_CHECKER_REJECTION_AFTER_COMMIT");
  o2b_print_result(o2b_wrap(completed, O2bCompleted, [|visible|]))
}
