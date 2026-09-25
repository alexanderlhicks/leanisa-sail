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
function d_work(pc : kword) -> o2a_work(65536) = struct {
  registers = struct { pc = pc, fp = 0x0000000000000001 },
  cells = v_empty(),
  origins = vector_init(65536, O2aUnknown),
  pending = [||], events = [||],
  components = None(),
  current_opcode = O2aNoOpcode, status = O2aRunning,
  phase = O2aInputPhase, failing_index = 0, failing_other = 0,
  pending_reason = O2aNoPendingIssue, steps = 0
}


function sparse_boundary_tests() -> unit = {
  let low = o2s_entry(0, false, sail_zeros(192));
  let high = o2s_entry(4294967295, true, embed_k(0x0000000000000009));
  var tree : option(sp_t32) = sp_put(None(), 0, low);
  tree = sp_put(tree, 4294967295, high);
  assert(match sp_get(tree, 4294967295) {
    Some(x) => x.parent == 4294967295 & x.fixed & x.value == embed_k(0x0000000000000009),
    None() => false
  }, "maximum key stored");
  assert(match sp_get(tree, 0) { Some(x) => x.parent == 0, None() => false },
    "zero retained");
  assert(match sp_get(tree, 4294967296) { None() => true, Some(_) => false },
    "out-of-range key rejected");
  assert(o2s_find_fuel(tree, 4294967296, 4294967295, 33) == Some(4294967295),
    "maximum key root");
  var bad = low;
  bad.parent = 9;
  tree = sp_put(tree, 0, bad);
  assert(o2s_find_fuel(tree, 4294967296, 0, 33) == None(),
    "missing parent rejected");
  bad.parent = 0;
  tree = sp_put(tree, 0, bad);
  assert(o2s_find_fuel(tree, 4294967296, 0, 0) == None(),
    "exhausted fuel rejected");
  let bad_target = o2a_pending(d_work(0x0000000000000001), 65536, 3);
  let no_target_pair : bool = match bad_target.pending { [||] => true, _ => false };
  let no_target_map : bool = match bad_target.components { None() => true, Some(_) => false };
  assert(bad_target.status == O2aAddressOutOfBounds &
    bad_target.failing_index == 65536 &
    no_target_pair & no_target_map,
    "invalid target rejected before pair and map mutation");
  let bad_source = o2a_pending(d_work(0x0000000000000001), 3, 65536);
  let no_source_pair : bool = match bad_source.pending { [||] => true, _ => false };
  let no_source_map : bool = match bad_source.components { None() => true, Some(_) => false };
  assert(bad_source.status == O2aAddressOutOfBounds &
    bad_source.failing_index == 65536 &
    no_source_pair & no_source_map,
    "invalid source rejected before pair and map mutation")
}

function main() -> unit = {
  sparse_boundary_tests();
  var a2 : vector(2, o2a_advice) = vector_init(2, v_pointer());
  a2[1] = v_nine(4);
  v_emit("ONE_KNOWN", v_run(v_two(v_pair1()), v_empty(), a2, 1), O2aGeneratedHalted, O2aCheckedHalted);
  var p : vector(4, instruction) = v_four();
  p[0] = v_pair1(); p[1] = v_pair2();
  a2[1] = v_nine(5);
  v_emit("CHAIN", v_run(p, v_empty(), a2, 2), O2aGeneratedPrefix, O2aCheckedPrefix);
  p[0] = v_pair2(); p[1] = v_pair1();
  v_emit("CHAIN_REVERSED", v_run(p, v_empty(), a2, 2), O2aGeneratedPrefix, O2aCheckedPrefix);
  var a1 : vector(1, o2a_advice) = vector_init(1, v_pointer());
  p[0] = v_pair1(); p[1] = v_pair2();
  v_emit("DEFAULT", v_run(p, v_empty(), a1, 2), O2aGeneratedPrefix, O2aCheckedPrefix);
  p[1] = Set(gpow(0x0000000000000004), embed_k(0x0000000000000009));
  p[2] = Xor(gpow(0x0000000000000003), gpow(0x0000000000000006), gpow(0x0000000000000007));
  v_emit("LATE_SET", v_run(p, v_empty(), a1, 3), O2aGeneratedHalted, O2aCheckedHalted);
  p[1] = Xor(gpow(0x0000000000000003), gpow(0x0000000000000006), gpow(0x0000000000000007));
  p[2] = Set(gpow(0x0000000000000004), embed_k(0x0000000000000009));
  v_emit("EAGER_ZERO", v_run(p, v_empty(), a1, 3), O2aAssignmentConflict, O2aDiagnosticPartial);
  p = v_four(); p[0] = v_pair1(); p[1] = v_pair2();
  var a3 : vector(3, o2a_advice) = vector_init(3, v_pointer());
  a3[1] = v_five(3); a3[2] = v_nine(5);
  v_emit("FIXED_CONFLICT", v_run(p, v_empty(), a3, 2), O2aEqualityConflict, O2aDiagnosticPartial);
  p[1] = Deref(gpow(0x0000000000000002), gpow(0x0000000000000002), gpow(0x0000000000000004), Cell);
  a2[1] = v_nine(4);
  v_emit("REPEATED", v_run(p, v_empty(), a2, 2), O2aGeneratedPrefix, O2aCheckedPrefix);
  a2[0] = struct { index = 2, value = embed_k(0x0000000000000001) };
  a2[1] = struct { index = 3, value = embed_k(0x0000000000000001) };
  v_emit("POINTER_ALIAS", v_run(v_two(Deref(gpow(0x0000000000000002), gpow(0x0000000000000002), gpow(0x0000000000000003), Cell)), v_empty(), a2, 1), O2aGeneratedHalted, O2aCheckedHalted);
  a1[0] = struct { index = 2, value = 0x000000000000000100000000000000000000000000000000 };
  v_emit("ADDRESS_PRIORITY", v_run(v_two(v_pair1()), v_empty(), a1, 1), O2aAddressOutOfBounds, O2aDiagnosticPartial);
  var init = v_empty(); init[0] = Some(embed_k(0x0000000000000001));
  var bad : vector(1, o2a_advice) = vector_init(1, struct { index = 100000, value = embed_k(0x0000000000000001) });
  v_emit("PUBLIC_PRIORITY", v_run(v_two(Set(0x0000000000000000, sail_zeros(192))), init, bad, 0), O2aPublicInputConflict, O2aDiagnosticPartial);
  p = v_four(); p[0] = v_pair1();
  p[1] = Jump(gpow(0x0000000000000005), gpow(0x0000000000000006), gpow(0x0000000000000007));
  var a5 : vector(5, o2a_advice) = vector_init(5, v_pointer());
  a5[1] = v_nine(4);
  a5[2] = struct { index = 5, value = embed_k(0x0000000000000001) };
  a5[3] = struct { index = 6, value = embed_k(0x0000000000000008) };
  a5[4] = struct { index = 7, value = embed_k(0x0000000000000002) };
  v_emit("TERMINAL_FRAME", v_run(p, v_empty(), a5, 2), O2aTerminalFrame, O2aDiagnosticComplete)
}
