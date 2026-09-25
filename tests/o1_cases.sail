// Directed O1 controls.  The full result of every case is printed through
// o1_print_result and compared between the generated C and Lean executables.

function o1_empty_advice() -> vector(0, o1_advice) =
  vector_init(0, struct { index = 0, value = sail_zeros(192) })

function o1_empty_initial() -> vector(65536, option(eword)) =
  vector_init(65536, None())

val o1_case_run : forall 'p 'm 'a, 'p >= 1 & 'm >= 2 & 'a >= 0.
  (vector('p, instruction), vector('m, option(eword)),
   vector('a, o1_advice), bits(256), nat) -> o1_result('m)
function o1_case_run(program, initial, advice, public_input, fuel) = {
  let input : o1_input('p, 'm, 'a) = struct {
    program = program, initial = initial,
    advice = advice, public_input = public_input, fuel = fuel
  };
  forward_run(input)
}

function o1_emit_case(label : string, result : o1_result(65536),
  expected : o1_status, tag : o1_image_tag) -> unit = {
  assert(result.status == expected, label);
  assert(result.image_tag == tag, label);
  print_endline(label);
  o1_print_result(result)
}

function o1_two_program(ins : instruction) -> vector(2, instruction) = {
  var program : vector(2, instruction) = vector_init(2, Set(0x0000000000000001, sail_zeros(192)));
  program[0] = ins;
  program
}

function o1_test_set() -> unit = {
  let program = o1_two_program(Set(gpow(0x0000000000000002), embed_k(0x0000000000000007)));
  let result = o1_case_run(program, o1_empty_initial(), o1_empty_advice(), sail_zeros(256), 1);
  assert(result.image[2] == embed_k(0x0000000000000007), "SET output");
  assert(result.cells[100] == None() & result.image[100] == sail_zeros(192),
    "unassigned cell defaults only in completed image");
  assert(result.checker_result == Some(struct {
    state = struct { pc = 0x0000000000000002, fp = 0x0000000000000001 },
    verdict = Halted
  }), "SET checker result");
  o1_emit_case("SET", result, O1GeneratedHalted, O1CheckedHalted)
}

function o1_test_xor_mul() -> unit = {
  let a = gpow(0x0000000000000002);
  let b = gpow(0x0000000000000003);
  let c = gpow(0x0000000000000004);
  var advice : vector(2, o1_advice) = vector_init(2, struct { index = 0, value = sail_zeros(192) });
  advice[0] = struct { index = 2, value = embed_k(0x0000000000000003) };
  advice[1] = struct { index = 3, value = embed_k(0x0000000000000005) };
  let xor_result = o1_case_run(o1_two_program(Xor(a, b, c)),
    o1_empty_initial(), advice, sail_zeros(256), 1);
  assert(xor_result.image[4] == embed_k(0x0000000000000006), "XOR result");
  o1_emit_case("XOR_ADVISED", xor_result, O1GeneratedHalted, O1CheckedHalted);
  let mul_result = o1_case_run(o1_two_program(Mul(a, b, c)),
    o1_empty_initial(), advice, sail_zeros(256), 1);
  assert(mul_result.image[4] == emul(advice[0].value, advice[1].value), "MUL result");
  o1_emit_case("MUL_ADVISED", mul_result, O1GeneratedHalted, O1CheckedHalted)
}

function o1_test_deref() -> unit = {
  let pointer = gpow(0x0000000000000002);
  let target_factor = gpow(0x0000000000000002);
  let source = gpow(0x0000000000000004);
  var advice : vector(3, o1_advice) = vector_init(3, struct { index = 0, value = sail_zeros(192) });
  advice[0] = struct { index = 2, value = embed_k(0x0000000000000002) };
  advice[1] = struct { index = 3, value = embed_k(0x0000000000000009) };
  advice[2] = struct { index = 4, value = embed_k(0x0000000000000009) };
  let cell = o1_case_run(o1_two_program(Deref(pointer, target_factor, source, Cell)),
    o1_empty_initial(), advice, sail_zeros(256), 1);
  o1_emit_case("DEREF_CELL_EQUAL", cell, O1GeneratedHalted, O1CheckedHalted);
  var one_advice : vector(2, o1_advice) = vector_init(2, advice[0]);
  one_advice[0] = advice[0];
  one_advice[1] = advice[2];
  let pending = o1_case_run(o1_two_program(Deref(pointer, target_factor, source, Cell)),
    o1_empty_initial(), one_advice, sail_zeros(256), 1);
  assert(pending.pending_reason == O1OneDefaulted, "one Cell endpoint defaulted");
  assert(pending.checker_result == None(), "pending mismatch not checked");
  o1_emit_case("DEREF_CELL_ONE_UNKNOWN", pending,
    O1PendingUnresolved, O1DiagnosticComplete);
  let pc = o1_case_run(o1_two_program(Deref(pointer, target_factor, source, Pc)),
    o1_empty_initial(), o1_empty_advice(), sail_zeros(256), 1);
  // The unknown pointer is eagerly fixed to zero, so target addressing fails.
  o1_emit_case("DEREF_PC_ZERO_POINTER", pc,
    O1AddressOutOfBounds, O1DiagnosticPartial);
  var pointer_advice : vector(1, o1_advice) = vector_init(1, advice[0]);
  let pc_good = o1_case_run(o1_two_program(Deref(pointer, target_factor, source, Pc)),
    o1_empty_initial(), pointer_advice, sail_zeros(256), 1);
  assert(pc_good.image[3] == embed_k(0x0000000000000004), "DEREF Pc output");
  o1_emit_case("DEREF_PC", pc_good, O1GeneratedHalted, O1CheckedHalted);
  let fp_good = o1_case_run(o1_two_program(Deref(pointer, target_factor, source, Fp)),
    o1_empty_initial(), pointer_advice, sail_zeros(256), 1);
  assert(fp_good.image[3] == embed_k(0x0000000000000001), "DEREF Fp output");
  o1_emit_case("DEREF_FP", fp_good, O1GeneratedHalted, O1CheckedHalted);
  let bad_source = o1_case_run(o1_two_program(Deref(pointer, target_factor,
    0x0000000000000000, Pc)), o1_empty_initial(), pointer_advice,
    sail_zeros(256), 1);
  o1_emit_case("DEREF_PC_SOURCE_ACCESS", bad_source,
    O1AddressOutOfBounds, O1DiagnosticPartial);
  pointer_advice[0] = struct { index = 2,
    value = 0x000000000000000100000000000000000000000000000002 };
  let bad_pointer = o1_case_run(o1_two_program(Deref(pointer, target_factor,
    source, Cell)), o1_empty_initial(), pointer_advice,
    sail_zeros(256), 1);
  o1_emit_case("DEREF_POINTER_HIGH", bad_pointer,
    O1OperandOutsideK, O1DiagnosticPartial);
  pointer_advice[0] = struct { index = 2,
    value = 0x000000000000000100000000000000000000000000000000 };
  let access_priority = o1_case_run(o1_two_program(Deref(pointer, target_factor,
    source, Cell)), o1_empty_initial(), pointer_advice,
    sail_zeros(256), 1);
  o1_emit_case("DEREF_TARGET_ACCESS_PRIORITY", access_priority,
    O1AddressOutOfBounds, O1DiagnosticPartial)
}

function o1_test_blake() -> unit = {
  let program = o1_two_program(Blake2s(
    gpow(0x0000000000000002), gpow(0x0000000000000003),
    gpow(0x0000000000000004), gpow(0x0000000000000005),
    gpow(0x0000000000000006), gpow(0x0000000000000009),
    gpow(0x0000000000000008)));
  let result = o1_case_run(program, o1_empty_initial(), o1_empty_advice(),
    sail_zeros(256), 1);
  let digest = blake_compress(sail_zeros(512), sail_zeros(256), sail_zeros(128));
  assert(result.image[9] == (0x0000000000000000 @ digest[127..0]), "BLAKE first chunk");
  assert(result.image[10] == (0x0000000000000000 @ digest[255..128]), "BLAKE second chunk");
  o1_emit_case("BLAKE_ZERO", result, O1GeneratedHalted, O1CheckedHalted);
  let advice : vector(1, o1_advice) = vector_init(1, struct {
    index = 10, value = (0x0000000000000000 @ (digest[255..128] ^^ sail_ones(128)))
  });
  let conflict = o1_case_run(program, o1_empty_initial(), advice, sail_zeros(256), 1);
  assert(conflict.cells[9] == Some(0x0000000000000000 @ digest[127..0]),
    "first BLAKE output retained");
  assert(conflict.registers.pc == 0x0000000000000001, "failed BLAKE leaves registers");
  o1_emit_case("BLAKE_SECOND_OUTPUT_CONFLICT", conflict,
    O1AssignmentConflict, O1DiagnosticPartial)
}

function o1_test_fuel_and_input() -> unit = {
  let empty = o1_empty_initial();
  let singleton : vector(1, instruction) = vector_init(1,
    Deref(0x0000000000000000, 0x0000000000000000,
      0x0000000000000000, Cell));
  let sentinel = o1_case_run(singleton, empty, o1_empty_advice(), sail_zeros(256), 0);
  o1_emit_case("SINGLETON_SENTINEL_ZERO_FUEL", sentinel,
    O1GeneratedHalted, O1CheckedHalted);
  let program = o1_two_program(Set(gpow(0x0000000000000002),
    embed_k(0x0000000000000007)));
  let fuel_prefix = o1_case_run(program, empty, o1_empty_advice(), sail_zeros(256), 0);
  o1_emit_case("ZERO_FUEL_PREFIX", fuel_prefix, O1GeneratedPrefix, O1CheckedPrefix);
  let exact = o1_case_run(program, empty, o1_empty_advice(), sail_zeros(256), 1);
  o1_emit_case("SENTINEL_EXACT_FUEL", exact, O1GeneratedHalted, O1CheckedHalted);
  var bad_initial = empty;
  bad_initial[0] = Some(embed_k(0x0000000000000001));
  let public_conflict = o1_case_run(program, bad_initial, o1_empty_advice(),
    sail_zeros(256), 0);
  o1_emit_case("PUBLIC_CONFLICT_BEFORE_FUEL", public_conflict,
    O1PublicInputConflict, O1DiagnosticPartial);
  let bad_advice : vector(1, o1_advice) = vector_init(1,
    struct { index = 65536, value = sail_zeros(192) });
  let advice_failure = o1_case_run(program, empty, bad_advice,
    sail_zeros(256), 0);
  o1_emit_case("ADVICE_BOUNDS_BEFORE_FUEL", advice_failure,
    O1AdviceOutOfBounds, O1DiagnosticPartial)
}

function o1_test_jump() -> unit = {
  var program : vector(4, instruction) = vector_init(4,
    Set(gpow(0x0000000000000002), sail_zeros(192)));
  program[0] = Jump(gpow(0x0000000000000002),
    gpow(0x0000000000000003), gpow(0x0000000000000004));
  program[2] = Jump(gpow(0x0000000000000004),
    gpow(0x0000000000000005), gpow(0x0000000000000006));
  var advice : vector(6, o1_advice) = vector_init(6,
    struct { index = 0, value = sail_zeros(192) });
  advice[0] = struct { index = 2, value = embed_k(0x0000000000000001) };
  advice[1] = struct { index = 3, value = embed_k(0x0000000000000004) };
  advice[2] = struct { index = 4, value = embed_k(0x0000000000000002) };
  advice[3] = struct { index = 5, value = embed_k(0x0000000000000001) };
  advice[4] = struct { index = 6, value = embed_k(0x0000000000000008) };
  advice[5] = struct { index = 7, value = embed_k(0x0000000000000001) };
  let changed = o1_case_run(program, o1_empty_initial(), advice,
    sail_zeros(256), 2);
  assert(changed.registers.fp == 0x0000000000000001, "frame restored");
  o1_emit_case("JUMP_CHANGE_FRAME", changed, O1GeneratedHalted, O1CheckedHalted);
  var one_step : vector(3, o1_advice) = vector_init(3, advice[0]);
  one_step[0] = advice[0];
  one_step[1] = struct { index = 3, value = embed_k(0x0000000000000002) };
  one_step[2] = advice[2];
  let bad_frame = o1_case_run(o1_two_program(program[0]),
    o1_empty_initial(), one_step, sail_zeros(256), 1);
  assert(bad_frame.checker_result == Some(struct {
    state = struct { pc = 0x0000000000000002, fp = 0x0000000000000002 },
    verdict = BadValue
  }), "terminal bad frame checker");
  o1_emit_case("JUMP_TERMINAL_BAD_FRAME", bad_frame,
    O1TerminalFrame, O1DiagnosticComplete);
  var bad_k : vector(3, o1_advice) = vector_init(3, advice[0]);
  bad_k[0] = struct { index = 2, value = sail_zeros(192) };
  bad_k[1] = struct {
    index = 3,
    value = 0x000000000000000100000000000000000000000000000000
  };
  bad_k[2] = struct { index = 4, value = sail_zeros(192) };
  let fallthrough = o1_case_run(o1_two_program(program[0]),
    o1_empty_initial(), bad_k, sail_zeros(256), 1);
  assert(fallthrough.failing_index == 3, "jump destination K diagnostic index");
  o1_emit_case("JUMP_FALLTHROUGH_K_GUARD", fallthrough,
    O1OperandOutsideK, O1DiagnosticPartial);
  bad_k[1] = struct { index = 3, value = sail_zeros(192) };
  bad_k[2] = struct { index = 4,
    value = 0x000000000000000100000000000000000000000000000000 };
  let late_k = o1_case_run(o1_two_program(program[0]),
    o1_empty_initial(), bad_k, sail_zeros(256), 1);
  assert(late_k.failing_index == 4, "jump frame K diagnostic index");
  o1_emit_case("JUMP_FRAME_K_GUARD", late_k,
    O1OperandOutsideK, O1DiagnosticPartial)
}

function o1_test_precedence_and_access() -> unit = {
  var short : vector(2, option(eword)) = vector_init(2, None());
  short[0] = Some(embed_k(0x0000000000000001));
  let invalid_advice : vector(1, o1_advice) = vector_init(1,
    struct { index = 100000, value = embed_k(0x0000000000000001) });
  let malformed = o1_case_run(o1_two_program(Set(0x0000000000000000,
    sail_zeros(192))), short, invalid_advice, sail_zeros(256), 0);
  assert(malformed.status == O1InvalidShape, "shape before public/advice/fuel");
  print_endline("INVALID_SHAPE_PRIORITY");
  o1_print_result(malformed);
  var initial = o1_empty_initial();
  initial[0] = Some(embed_k(0x0000000000000001));
  let public_first = o1_case_run(o1_two_program(Set(0x0000000000000000,
    sail_zeros(192))), initial, invalid_advice, sail_zeros(256), 0);
  o1_emit_case("PUBLIC_BEFORE_ADVICE", public_first,
    O1PublicInputConflict, O1DiagnosticPartial);
  var duplicate : vector(3, o1_advice) = vector_init(3,
    struct { index = 2, value = embed_k(0x0000000000000003) });
  let same = o1_case_run(o1_two_program(Set(gpow(0x0000000000000002),
    embed_k(0x0000000000000003))), o1_empty_initial(), duplicate,
    sail_zeros(256), 1);
  o1_emit_case("DUPLICATE_ADVICE", same,
    O1GeneratedHalted, O1CheckedHalted);
  duplicate[2] = struct { index = 2, value = embed_k(0x0000000000000004) };
  let conflict = o1_case_run(o1_two_program(Set(gpow(0x0000000000000002),
    embed_k(0x0000000000000003))), o1_empty_initial(), duplicate,
    sail_zeros(256), 0);
  o1_emit_case("ADVICE_FIRST_CONFLICT", conflict,
    O1AdviceConflict, O1DiagnosticPartial);
  let zero_access = o1_case_run(o1_two_program(Set(0x0000000000000000,
    sail_zeros(192))), o1_empty_initial(), o1_empty_advice(),
    sail_zeros(256), 1);
  o1_emit_case("RAW_ZERO_ACCESS", zero_access,
    O1AddressOutOfBounds, O1DiagnosticPartial);
  let high = gpow(0x000000000000ffff);
  let last_cv = o1_case_run(o1_two_program(Blake2s(
    gpow(0x0000000000000002), gpow(0x0000000000000003),
    gpow(0x0000000000000004), gpow(0x0000000000000005),
    high, gpow(0x0000000000000009), gpow(0x0000000000000008))),
    o1_empty_initial(), o1_empty_advice(), sail_zeros(256), 1);
  o1_emit_case("BLAKE_LAST_CV_ACCESS", last_cv,
    O1AddressOutOfBounds, O1DiagnosticPartial);
  let last_output = o1_case_run(o1_two_program(Blake2s(
    gpow(0x0000000000000002), gpow(0x0000000000000003),
    gpow(0x0000000000000004), gpow(0x0000000000000005),
    gpow(0x0000000000000006), high, gpow(0x0000000000000008))),
    o1_empty_initial(), o1_empty_advice(), sail_zeros(256), 1);
  o1_emit_case("BLAKE_LAST_OUTPUT_ACCESS", last_output,
    O1AddressOutOfBounds, O1DiagnosticPartial)
}

function o1_test_eager_incompleteness() -> unit = {
  let a = gpow(0x0000000000000002);
  let b = gpow(0x0000000000000003);
  let c = gpow(0x0000000000000004);
  var program : vector(4, instruction) = vector_init(4,
    Set(a, sail_zeros(192)));
  program[0] = Xor(a, a, b);
  program[1] = Set(a, embed_k(0x0000000000000001));
  let xor = o1_case_run(program, o1_empty_initial(), o1_empty_advice(),
    sail_zeros(256), 2);
  assert(xor.cells[2] == Some(sail_zeros(192)), "XOR early default retained");
  assert(xor.registers.pc == 0x0000000000000002, "XOR failure keeps register");
  o1_emit_case("XOR_CANCELLATION_EARLY_DEFAULT", xor,
    O1AssignmentConflict, O1DiagnosticPartial);
  var sail_image : vector(65536, eword) = vector_init(65536, sail_zeros(192));
  sail_image[2] = embed_k(0x0000000000000001);
  assert(run(program, sail_image, sail_zeros(256), 2).verdict == OutOfFuel,
    "XOR cancellation remains Sail-valid");
  program[0] = Mul(a, b, c);
  let mul = o1_case_run(program, o1_empty_initial(), o1_empty_advice(),
    sail_zeros(256), 2);
  o1_emit_case("MUL_EARLY_DEFAULT", mul,
    O1AssignmentConflict, O1DiagnosticPartial);
  assert(run(program, sail_image, sail_zeros(256), 2).verdict == OutOfFuel,
    "MUL zero factor permits Sail image");
  program[0] = Jump(a, b, c);
  let jump = o1_case_run(program, o1_empty_initial(), o1_empty_advice(),
    sail_zeros(256), 2);
  o1_emit_case("JUMP_LATE_CONDITION", jump,
    O1AssignmentConflict, O1DiagnosticPartial)
}

function o1_test_cell_pairs_and_aliases() -> unit = {
  let pointer = gpow(0x0000000000000002);
  let target = gpow(0x0000000000000002);
  let source = gpow(0x0000000000000004);
  var advice : vector(3, o1_advice) = vector_init(3,
    struct { index = 2, value = embed_k(0x0000000000000002) });
  advice[0] = struct { index = 2, value = embed_k(0x0000000000000002) };
  advice[1] = struct { index = 3, value = embed_k(0x0000000000000005) };
  advice[2] = struct { index = 4, value = embed_k(0x0000000000000009) };
  let different = o1_case_run(o1_two_program(Deref(pointer, target, source, Cell)),
    o1_empty_initial(), advice, sail_zeros(256), 1);
  assert(different.pending_reason == O1BothFixed, "both Cell endpoints fixed");
  o1_emit_case("DEREF_CELL_BOTH_FIXED_DIFFERENT", different,
    O1PendingUnresolved, O1DiagnosticComplete);
  var program : vector(4, instruction) = vector_init(4,
    Set(gpow(0x0000000000000006), sail_zeros(192)));
  program[0] = Deref(pointer, target, source, Cell);
  program[1] = Deref(pointer, target, gpow(0x0000000000000005), Cell);
  var connected : vector(4, o1_advice) = vector_init(4, advice[0]);
  connected[0] = advice[0];
  connected[1] = struct { index = 3, value = embed_k(0x0000000000000009) };
  connected[2] = advice[2];
  connected[3] = struct { index = 5, value = embed_k(0x0000000000000009) };
  let pairs = o1_case_run(program, o1_empty_initial(), connected,
    sail_zeros(256), 2);
  o1_emit_case("DEREF_CONNECTED_PAIRS", pairs,
    O1GeneratedPrefix, O1CheckedPrefix);
  var pointer_alias : vector(2, o1_advice) = vector_init(2, advice[0]);
  pointer_alias[0] = struct { index = 2, value = embed_k(0x0000000000000001) };
  pointer_alias[1] = struct { index = 3, value = embed_k(0x0000000000000001) };
  let aliased = o1_case_run(o1_two_program(Deref(pointer, target,
    gpow(0x0000000000000003), Cell)), o1_empty_initial(), pointer_alias,
    sail_zeros(256), 1);
  o1_emit_case("DEREF_POINTER_TARGET_ALIAS", aliased,
    O1GeneratedHalted, O1CheckedHalted)
}

function o1_test_control_boundaries() -> unit = {
  let a = gpow(0x0000000000000002);
  let b = gpow(0x0000000000000003);
  let c = gpow(0x0000000000000004);
  var advice : vector(3, o1_advice) = vector_init(3,
    struct { index = 2, value = embed_k(0x0000000000000001) });
  advice[0] = struct { index = 2, value = embed_k(0x0000000000000001) };
  advice[1] = struct { index = 3, value = embed_k(0x0000000000000001) };
  advice[2] = struct { index = 4, value = embed_k(0x0000000000000001) };
  let loop = o1_case_run(o1_two_program(Jump(a, b, c)),
    o1_empty_initial(), advice, sail_zeros(256), 2);
  assert(loop.registers.pc == 0x0000000000000001 & loop.steps == 2,
    "repeated PC exact fuel");
  o1_emit_case("REPEATED_PC_PREFIX", loop,
    O1GeneratedPrefix, O1CheckedPrefix);
  var failing : vector(4, instruction) = vector_init(4,
    Set(a, sail_zeros(192)));
  failing[0] = Set(a, sail_zeros(192));
  failing[1] = Set(0x0000000000000000, sail_zeros(192));
  let before = o1_case_run(failing, o1_empty_initial(), o1_empty_advice(),
    sail_zeros(256), 1);
  o1_emit_case("FUEL_BEFORE_BAD_STEP", before,
    O1GeneratedPrefix, O1CheckedPrefix);
  let after = o1_case_run(failing, o1_empty_initial(), o1_empty_advice(),
    sail_zeros(256), 2);
  o1_emit_case("BAD_STEP_AFTER_FUEL", after,
    O1AddressOutOfBounds, O1DiagnosticPartial);
  advice[1] = struct { index = 3, value = embed_k(gpow(0x0000000000000064)) };
  let missing = o1_case_run(o1_two_program(Jump(a, b, c)),
    o1_empty_initial(), advice, sail_zeros(256), 2);
  o1_emit_case("INVALID_NEXT_FETCH", missing,
    O1FetchFailure, O1DiagnosticPartial)
}

function o1_test_chunk_and_output_guards() -> unit = {
  let program = o1_two_program(Blake2s(
    gpow(0x0000000000000002), gpow(0x0000000000000003),
    gpow(0x0000000000000004), gpow(0x0000000000000005),
    gpow(0x0000000000000006), gpow(0x0000000000000009),
    gpow(0x0000000000000008)));
  var input : vector(1, o1_advice) = vector_init(1,
    struct { index = 2,
      value = 0x000000000000000100000000000000000000000000000000 });
  let high = o1_case_run(program, o1_empty_initial(), input,
    sail_zeros(256), 1);
  assert(high.failing_index == 2, "first BLAKE chunk diagnostic index");
  o1_emit_case("BLAKE_HIGH_INPUT", high,
    O1OperandOutsideChunk, O1DiagnosticPartial);
  input[0] = struct { index = 7,
    value = 0x000000000000000100000000000000000000000000000000 };
  let late_chunk = o1_case_run(program, o1_empty_initial(), input,
    sail_zeros(256), 1);
  assert(late_chunk.failing_index == 7, "later BLAKE chunk diagnostic index");
  o1_emit_case("BLAKE_LATE_CHUNK_GUARD", late_chunk,
    O1OperandOutsideChunk, O1DiagnosticPartial);
  input[0] = struct { index = 8,
    value = 0x0000000000000000fedcba9876543210ffffffffffffffff };
  let flags = o1_case_run(program, o1_empty_initial(), input,
    sail_zeros(256), 1);
  let digest = blake_compress(sail_zeros(512), sail_zeros(256),
    input[0].value[127..0]);
  assert(flags.image[9] == (0x0000000000000000 @ digest[127..0]),
    "all 128 metadata bits used");
  o1_emit_case("BLAKE_RAW_METADATA", flags,
    O1GeneratedHalted, O1CheckedHalted);
  var initial = o1_empty_initial();
  initial[9] = Some(0x000000000000000100000000000000000000000000000000);
  let high_output = o1_case_run(program, initial, o1_empty_advice(),
    sail_zeros(256), 1);
  o1_emit_case("BLAKE_HIGH_OUTPUT_CONFLICT", high_output,
    O1AssignmentConflict, O1DiagnosticPartial)
}

function o1_test_aliases_and_last_cell() -> unit = {
  let a = gpow(0x0000000000000002);
  let b = gpow(0x0000000000000003);
  let last = gpow(0x000000000000ffff);
  let high : eword =
    0x0123456789abcdef00000000000000000000000000000007;
  let last_result = o1_case_run(o1_two_program(Set(last, high)),
    o1_empty_initial(), o1_empty_advice(), sail_zeros(256), 1);
  assert(last_result.image[65535] == high, "last cell SET full high limbs");
  o1_emit_case("SET_LAST_CELL_HIGH_WORD", last_result,
    O1GeneratedHalted, O1CheckedHalted);
  let advice : vector(1, o1_advice) = vector_init(1,
    struct { index = 2, value = embed_k(0x0000000000000003) });
  let xor_alias = o1_case_run(o1_two_program(Xor(a, a, b)),
    o1_empty_initial(), advice, sail_zeros(256), 1);
  assert(xor_alias.image[3] == sail_zeros(192), "XOR aliases cancel");
  o1_emit_case("XOR_OPERAND_ALIAS", xor_alias,
    O1GeneratedHalted, O1CheckedHalted);
  let mul_alias = o1_case_run(o1_two_program(Mul(a, a, b)),
    o1_empty_initial(), advice, sail_zeros(256), 1);
  assert(mul_alias.image[3] == emul(advice[0].value, advice[0].value),
    "MUL alias uses actual multiplication");
  o1_emit_case("MUL_OPERAND_ALIAS", mul_alias,
    O1GeneratedHalted, O1CheckedHalted);
  let blake_alias = o1_case_run(o1_two_program(Blake2s(a, a, a, a,
    gpow(0x0000000000000004), gpow(0x0000000000000006), a)),
    o1_empty_initial(), o1_empty_advice(), sail_zeros(256), 1);
  o1_emit_case("BLAKE_INPUT_ALIAS", blake_alias,
    O1GeneratedHalted, O1CheckedHalted);
  let digest = blake_compress(sail_zeros(512), sail_zeros(256), sail_zeros(128));
  assert(digest[127..0] != sail_zeros(128), "zero-input BLAKE first chunk nonzero");
  let output_alias = o1_case_run(o1_two_program(Blake2s(
    a, b, gpow(0x0000000000000004), gpow(0x0000000000000005),
    gpow(0x0000000000000006), a, gpow(0x0000000000000008))),
    o1_empty_initial(), o1_empty_advice(), sail_zeros(256), 1);
  assert(output_alias.cells[2] == Some(sail_zeros(192)),
    "BLAKE observed zero cannot be overwritten");
  assert(output_alias.failing_index == 2, "BLAKE alias conflict index");
  o1_emit_case("BLAKE_OUTPUT_INPUT_ALIAS_CONFLICT", output_alias,
    O1AssignmentConflict, O1DiagnosticPartial)
}

function o1_test_pending_terminal_priority() -> unit = {
  let pointer = gpow(0x0000000000000002);
  var program : vector(4, instruction) = vector_init(4,
    Set(pointer, sail_zeros(192)));
  program[0] = Deref(pointer, pointer, gpow(0x0000000000000004), Cell);
  program[1] = Jump(gpow(0x0000000000000005),
    gpow(0x0000000000000006), gpow(0x0000000000000007));
  var advice : vector(5, o1_advice) = vector_init(5,
    struct { index = 2, value = embed_k(0x0000000000000002) });
  advice[0] = struct { index = 2, value = embed_k(0x0000000000000002) };
  advice[1] = struct { index = 4, value = embed_k(0x0000000000000009) };
  advice[2] = struct { index = 5, value = embed_k(0x0000000000000001) };
  advice[3] = struct { index = 6, value = embed_k(0x0000000000000008) };
  advice[4] = struct { index = 7, value = embed_k(0x0000000000000002) };
  let pending = o1_case_run(program, o1_empty_initial(), advice,
    sail_zeros(256), 2);
  assert(pending.registers.fp == 0x0000000000000002,
    "pending conflict reaches nonunit terminal frame");
  assert(pending.checker_result == None(), "pending conflict precedes checker");
  o1_emit_case("PENDING_BEFORE_BAD_FRAME", pending,
    O1PendingUnresolved, O1DiagnosticComplete)
}

function o1_cases() -> unit = {
  o1_test_set();
  o1_test_xor_mul();
  o1_test_deref();
  o1_test_blake();
  o1_test_fuel_and_input();
  o1_test_jump();
  o1_test_precedence_and_access();
  o1_test_eager_incompleteness();
  o1_test_cell_pairs_and_aliases();
  o1_test_control_boundaries();
  o1_test_chunk_and_output_guards();
  o1_test_aliases_and_last_cell();
  o1_test_pending_terminal_priority()
}

function main() -> unit = {
  o1_cases();
  print_endline("O1 CASES PASS")
}
