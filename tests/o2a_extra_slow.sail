$include <string.sail>

function v_empty() -> vector(65536, option(eword)) = vector_init(65536, None())
function v_pointer() -> o2a_advice = struct { index = 2, value = embed_k(0x0000000000000002) }
function v_nine(i : cell_index) -> o2a_advice = struct { index = i, value = embed_k(0x0000000000000009) }
function v_five(i : cell_index) -> o2a_advice = struct { index = i, value = embed_k(0x0000000000000005) }
function v_pair1() -> instruction = Deref(gpow(0x0000000000000002), gpow(0x0000000000000002), gpow(0x0000000000000004), Cell)
function v_pair2() -> instruction = Deref(gpow(0x0000000000000002), gpow(0x0000000000000003), gpow(0x0000000000000005), Cell)
function v_two(i : instruction) -> vector(2, instruction) = { var p : vector(2, instruction) = vector_init(2, Set(gpow(0x0000000000000008), sail_zeros(192))); p[0] = i; p }
function v_four() -> vector(4, instruction) = vector_init(4, Set(gpow(0x0000000000000008), sail_zeros(192)))
val v_run : forall 'p 'a, 'p >= 1 & 'a >= 0. (vector('p, instruction), vector(65536, option(eword)), vector('a, o2a_advice), nat) -> o2a_result(65536)
function v_run(p, initial, advice, fuel) = o2a_forward_run_parts(p, initial, advice, sail_zeros(256), fuel)
function v_emit(label : string, r : o2a_result(65536), s : o2a_status, t : o2a_image_tag) -> unit = { assert(r.status == s & r.image_tag == t, label); print_endline(label); o2a_print_result(r) }
function d_emit(label : string, r : o2a_result(65536)) -> unit = {
  print_endline(label); o2a_print_result(r)
}
function d_pair67() -> instruction =
  Deref(gpow(0x0000000000000002), gpow(0x0000000000000005),
    gpow(0x0000000000000007), Cell)
function d_self2() -> instruction =
  Deref(gpow(0x0000000000000002), gpow(0x0000000000000001),
    gpow(0x0000000000000002), Cell)
function d_work(pc : kword) -> o2a_work(65536) = struct {
  registers = struct { pc = pc, fp = 0x0000000000000001 },
  cells = v_empty(),
  origins = vector_init(65536, O2aUnknown),
  pending = [||], events = [||],
  current_opcode = O2aNoOpcode, status = O2aRunning,
  phase = O2aInputPhase, failing_index = 0, failing_other = 0,
  pending_reason = O2aNoPendingIssue, steps = 0
}

function main() -> unit = {
  var p : vector(4, instruction) = v_four();
  p[0] = v_pair1(); p[1] = d_pair67();
  var a1 : vector(1, o2a_advice) = vector_init(1, v_pointer());
  d_emit("DISJOINT_DEFAULT", v_run(p, v_empty(), a1, 2));

  p[0] = v_pair1(); p[1] = v_pair2();
  var a3 : vector(3, o2a_advice) = vector_init(3, v_pointer());
  a3[1] = v_nine(3); a3[2] = v_nine(5);
  d_emit("SAME_FIXED_MERGE", v_run(p, v_empty(), a3, 2));
  a3[2] = v_five(5);
  d_emit("DIFFERENT_FIXED_MERGE", v_run(p, v_empty(), a3, 2));

  var init = v_empty(); init[4] = Some(embed_k(0x0000000000000009));
  p[0] = v_pair1(); p[1] = Set(gpow(0x0000000000000008), sail_zeros(192));
  d_emit("INITIAL_FIXED", v_run(p, init, a1, 1));

  p[0] = v_pair1();
  p[1] = Deref(gpow(0x0000000000000002), gpow(0x0000000000000003),
    gpow(0x0000000000000003), Cell);
  d_emit("REVERSED_REPEAT", v_run(p, v_empty(), a1, 2));

  p[0] = d_self2();
  d_emit("SELF_PAIR", v_run(p, v_empty(), a1, 1));

  p[0] = v_pair1();
  p[1] = Set(gpow(0x0000000000000004), embed_k(0x0000000000000005));
  p[2] = Xor(gpow(0x0000000000000003), gpow(0x0000000000000006),
    gpow(0x0000000000000007));
  d_emit("SET_THEN_READ", v_run(p, v_empty(), a1, 3));

  p[0] = Xor(gpow(0x0000000000000003), gpow(0x0000000000000006),
    gpow(0x0000000000000007));
  p[1] = v_pair1();
  d_emit("READ_THEN_PAIR", v_run(p, v_empty(), a1, 2));

  p[0] = Xor(gpow(0x0000000000000003), gpow(0x0000000000000006),
    gpow(0x0000000000000007));
  p[1] = v_pair1();
  p[2] = Set(gpow(0x0000000000000004), embed_k(0x0000000000000009));
  d_emit("READ_PAIR_SET", v_run(p, v_empty(), a1, 3));

  var a2 : vector(2, o2a_advice) = vector_init(2, v_pointer());
  a2[1] = v_pointer();
  d_emit("DUPLICATE_ADVICE", v_run(v_two(v_pair1()), v_empty(), a2, 1));
  a2[1] = struct { index = 2, value = embed_k(0x0000000000000003) };
  d_emit("CONFLICT_ADVICE", v_run(v_two(v_pair1()), v_empty(), a2, 1));

  a1[0] = struct { index = 2, value = 0x000000000000000100000000000000000000000000000000 };
  d_emit("INVALID_POINTER", v_run(v_two(v_pair1()), v_empty(), a1, 1));
  let check_program = v_two(Set(gpow(0x0000000000000008), sail_zeros(192)));
  d_emit("CHECKER_REJECTED", o2a_complete(d_work(0x0000000000000002),
    check_program, sail_zeros(256), 1, OutOfFuel));
  d_emit("CHECKER_MISMATCH", o2a_complete(d_work(0x0000000000000001),
    check_program, sail_zeros(256), 1, Halted))
}
