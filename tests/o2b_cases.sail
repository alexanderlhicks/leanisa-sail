$include <string.sail>

function b_empty() -> vector(65536, option(eword)) = vector_init(65536, None())
function b_two(ins : instruction) -> vector(2, instruction) = {
  var p : vector(2, instruction) = vector_init(2,
    Set(gpow(0x0000000000000008), sail_zeros(192)));
  p[0] = ins;
  p
}
function b_four() -> vector(4, instruction) = vector_init(4,
  Set(gpow(0x0000000000000008), sail_zeros(192)))
function b_mul(a : int, b : int, c : int) -> instruction =
  Mul(gpow(get_slice_int(64, a, 0)), gpow(get_slice_int(64, b, 0)),
    gpow(get_slice_int(64, c, 0)))
function b_plan(at_step : nat, a : option(eword), b : option(eword)) -> o2b_plan =
  struct { step = at_step, a_value = a, b_value = b }
function b_advice(i : cell_index, value : eword) -> o2a_advice =
  struct { index = i, value = value }
val b_run : forall 'p 'a, 'p >= 1 & 'a >= 0.
  (vector('p, instruction), vector(65536, option(eword)),
   vector('a, o2a_advice), nat, list(o2b_plan)) -> o2b_result(65536)
function b_run(program, initial, advice, fuel, plans) =
  o2b_forward_run_parts(program, initial, advice, sail_zeros(256), fuel, plans)

val b_count_events : (list(o2a_event), o2a_event_kind) -> nat
function b_count_events(events, kind) = match events {
  [||] => 0,
  event :: rest => (if event.kind == kind then 1 else 0)
    + b_count_events(rest, kind)
}

val b_first_event_at : (list(o2a_event), o2a_event_kind, nat) -> nat
function b_first_event_at(events, kind, position) = match events {
  [||] => 999999,
  event :: rest => if event.kind == kind then position
    else b_first_event_at(rest, kind, position + 1)
}

function b_first_event(events : list(o2a_event),
  kind : o2a_event_kind) -> nat = b_first_event_at(events, kind, 0)

val b_irrelevant_plans : (nat, list(o2b_plan)) -> list(o2b_plan)
function b_irrelevant_plans(n, acc) = {
  if n == 0 then acc else b_irrelevant_plans(n - 1,
    b_plan(999, Some(sail_zeros(192)), None()) :: acc)
}
termination_measure b_irrelevant_plans(n, acc) = n

val b_matching_plans : (nat, list(o2b_plan)) -> list(o2b_plan)
function b_matching_plans(n, acc) = {
  if n == 0 then acc else b_matching_plans(n - 1,
    b_plan(0, Some(embed_k(0x0000000000000002)), None()) :: acc)
}
termination_measure b_matching_plans(n, acc) = n

function b_ok(label : string, result : o2b_result(65536),
  condition : bool) -> unit = {
  assert(condition, label);
  print_endline(label);
  o2b_print_result(result)
}

function main() -> unit = {
  let empty : vector(0, o2a_advice) = vector_init(0,
    b_advice(0, sail_zeros(192)));
  let two = embed_k(0x0000000000000002);
  let three = embed_k(0x0000000000000003);
  let four = emul(two, two);
  let six = emul(two, three);
  let one = embed_k(0x0000000000000001);
  let mul = b_mul(3, 4, 5);

  let baseline = o2a_forward_run_parts(b_two(mul), b_empty(), empty,
    sail_zeros(256), 1);
  let no_plan = b_run(b_two(mul), b_empty(), empty, 1, [||]);
  b_ok("EMPTY_PARITY", no_plan, no_plan.solver == O2bCompleted &
    no_plan.common == baseline);
  let unexecuted = b_run(b_two(mul), b_empty(), empty, 1,
    [|b_plan(9, Some(two), None())|]);
  b_ok("UNEXECUTED_PARITY", unexecuted, unexecuted.common == baseline &
    unexecuted.solver == O2bCompleted);

  let fresh = b_run(b_two(mul), b_empty(), empty, 1,
    [|b_plan(0, Some(two), Some(three))|]);
  b_ok("FRESH_ABC", fresh, fresh.solver == O2bCompleted &
    fresh.common.status == O2aGeneratedHalted &
    fresh.common.image_tag == O2aCheckedHalted &
    fresh.common.cells[3] == Some(two) &
    fresh.common.cells[4] == Some(three) &
    fresh.common.cells[5] == Some(six) &
    fresh.common.origins[3] == O2bMulAdvice &
    fresh.common.origins[4] == O2bMulAdvice &
    fresh.common.origins[5] == O2aOutput &
    b_count_events(fresh.common.events, O2bMulAdviceWrite) == 2 &
    b_first_event(fresh.common.events, O2aStepStart) <
      b_first_event(fresh.common.events, O2aAddressResolve) &
    b_first_event(fresh.common.events, O2aAddressResolve) <
      b_first_event(fresh.common.events, O2bMulAdviceWrite) &
    b_first_event(fresh.common.events, O2bMulAdviceWrite) <
      b_first_event(fresh.common.events, O2aObserve) &
    b_first_event(fresh.common.events, O2aObserve) <
      b_first_event(fresh.common.events, O2aOutputWrite) &
    b_first_event(fresh.common.events, O2aOutputWrite) <
      b_first_event(fresh.common.events, O2aStepSuccess));

  var fixed = b_empty();
  fixed[5] = Some(embed_k(0x0000000000000007));
  let exhausted = b_run(b_two(mul), fixed, empty, 1,
    [|b_plan(0, Some(two), Some(three))|]);
  b_ok("CANDIDATE_EXHAUSTION_PURE", exhausted, exhausted.solver ==
    O2bCandidatesExhausted & exhausted.common.image_tag ==
    O2aDiagnosticPartial & exhausted.common.cells[3] == None() &
    exhausted.common.cells[4] == None() &
    b_count_events(exhausted.common.events, O2bMulAdviceWrite) == 0 &
    b_count_events(exhausted.common.events, O2aAddressResolve) == 3);
  let candidates : list(o2b_plan) = [|
    b_plan(0, Some(two), Some(three)),
    b_plan(0, Some(one), Some(embed_k(0x0000000000000007)))
  |];
  let second = b_run(b_two(mul), fixed, empty, 1, candidates);
  let picked_second : bool = match second.choices {
    choice :: _ => choice.ordinal == 1,
    [||] => false
  };
  b_ok("SECOND_CANDIDATE", second, second.solver == O2bCompleted &
    second.common.status == O2aGeneratedHalted &
    second.common.cells[3] == Some(one) &
    second.common.cells[4] == Some(embed_k(0x0000000000000007)) &
    second.common.origins[3] == O2bMulAdvice &
    picked_second);

  let alias_ab = b_run(b_two(b_mul(3, 3, 5)), b_empty(), empty, 1,
    [|b_plan(0, Some(two), Some(two))|]);
  b_ok("ALIAS_A_B", alias_ab, alias_ab.common.status == O2aGeneratedHalted &
    alias_ab.common.cells[3] == Some(two) &
    alias_ab.common.cells[5] == Some(four));
  let alias_conflict = b_run(b_two(b_mul(3, 3, 5)), b_empty(), empty, 1,
    [|b_plan(0, Some(two), Some(three))|]);
  b_ok("ALIAS_A_B_REJECT", alias_conflict, alias_conflict.solver ==
    O2bCandidatesExhausted & alias_conflict.common.cells[3] == None());
  let alias_ca = b_run(b_two(b_mul(3, 4, 3)), b_empty(), empty, 1,
    [|b_plan(0, Some(two), Some(one))|]);
  b_ok("ALIAS_C_A", alias_ca, alias_ca.common.status == O2aGeneratedHalted &
    alias_ca.common.cells[3] == Some(two) &
    alias_ca.common.cells[4] == Some(one));
  let alias_all = b_run(b_two(b_mul(3, 3, 3)), b_empty(), empty, 1,
    [|b_plan(0, Some(one), None())|]);
  b_ok("ALIAS_ALL", alias_all, alias_all.common.status == O2aGeneratedHalted &
    alias_all.common.cells[3] == Some(one));
  let alias_all_bad = b_run(b_two(b_mul(3, 3, 3)), b_empty(), empty, 1,
    [|b_plan(0, Some(two), None())|]);
  b_ok("ALIAS_ALL_REJECT", alias_all_bad, alias_all_bad.solver ==
    O2bCandidatesExhausted);

  var p = b_four();
  p[0] = Deref(gpow(0x0000000000000002),
    gpow(0x0000000000000002), gpow(0x0000000000000004), Cell);
  p[1] = mul;
  let pointer : vector(1, o2a_advice) = vector_init(1, b_advice(2, two));
  let joined = b_run(p, b_empty(), pointer, 2,
    [|b_plan(1, Some(two), None())|]);
  b_ok("JOINED_ROOTS", joined, joined.solver == O2bCompleted &
    joined.common.status == O2aGeneratedPrefix &
    joined.common.cells[3] == Some(two) &
    joined.common.cells[4] == Some(two) &
    joined.common.cells[5] == Some(four));
  let joined_conflict = b_run(p, b_empty(), pointer, 2,
    [|b_plan(1, Some(two), Some(three))|]);
  b_ok("JOINED_ROOT_CONFLICT_PURE", joined_conflict, joined_conflict.solver ==
    O2bCandidatesExhausted & joined_conflict.common.cells[3] == None() &
    joined_conflict.common.cells[4] == None() &
    b_count_events(joined_conflict.common.events, O2bMulAdviceWrite) == 0);

  var one_fixed = b_empty();
  one_fixed[4] = Some(three); one_fixed[5] = Some(six);
  let missing_a = b_run(b_two(mul), one_fixed, empty, 1,
    [|b_plan(0, Some(two), None())|]);
  b_ok("ONE_MISSING_FACTOR", missing_a, missing_a.solver == O2bCompleted &
    missing_a.common.status == O2aGeneratedHalted &
    missing_a.common.cells[3] == Some(two) &
    missing_a.common.cells[5] == Some(six));

  var supplied = b_empty();
  supplied[3] = Some(two); supplied[4] = Some(three);
  let fixed_factors = b_run(b_two(mul), supplied, empty, 1,
    [|b_plan(0, Some(two), Some(three))|]);
  b_ok("FIXED_FACTORS_NOT_TARGETS", fixed_factors, fixed_factors.solver ==
    O2bCandidatesExhausted & fixed_factors.common.cells[5] == None());

  let bad_address = b_run(b_two(Mul(gpow(0x0000000000000003),
    0x0000000000000000, gpow(0x0000000000000005))), b_empty(),
    empty, 1, [|b_plan(0, None(), None())|]);
  b_ok("ADDRESS_BEFORE_MALFORMED", bad_address, bad_address.common.status ==
    O2aAddressOutOfBounds & bad_address.solver == O2bCompleted &
    b_count_events(bad_address.common.events, O2aAddressResolve) == 1 &
    b_count_events(bad_address.common.events, O2aAddressReject) == 1 &
    b_count_events(bad_address.common.events, O2bMulAdviceWrite) == 0);
  let long_irrelevant = b_irrelevant_plans(2048, [||]);
  let long_first = b_run(b_two(Mul(0x0000000000000000,
    gpow(0x0000000000000004), gpow(0x0000000000000005))),
    b_empty(), empty, 1, long_irrelevant);
  b_ok("LONG_LIST_FIRST_ADDRESS_PRIORITY", long_first,
    long_first.common.status == O2aAddressOutOfBounds &
    long_first.solver == O2bCompleted &
    b_count_events(long_first.common.events, O2aAddressResolve) == 0 &
    b_count_events(long_first.common.events, O2aAddressReject) == 1);
  let bad_output_address = b_run(b_two(Mul(gpow(0x0000000000000003),
    gpow(0x0000000000000004), 0x0000000000000000)), b_empty(),
    empty, 1, [|b_plan(0, None(), None())|]);
  b_ok("THIRD_ADDRESS_FAILURE", bad_output_address, bad_output_address.common.status ==
    O2aAddressOutOfBounds &
    b_count_events(bad_output_address.common.events, O2aAddressResolve) == 2 &
    b_count_events(bad_output_address.common.events, O2aAddressReject) == 1 &
    bad_output_address.solver == O2bCompleted);
  let long_third = b_run(b_two(Mul(gpow(0x0000000000000003),
    gpow(0x0000000000000004), 0x0000000000000000)), b_empty(),
    empty, 1, long_irrelevant);
  b_ok("LONG_LIST_THIRD_ADDRESS_PRIORITY", long_third,
    long_third.common.status == O2aAddressOutOfBounds &
    long_third.solver == O2bCompleted &
    b_count_events(long_third.common.events, O2aAddressResolve) == 2 &
    b_count_events(long_third.common.events, O2aAddressReject) == 1);
  let malformed = b_run(b_two(mul), b_empty(), empty, 1,
    [|b_plan(0, None(), None())|]);
  b_ok("MALFORMED_FETCHED_PLAN", malformed, malformed.solver == O2bMalformedPlan &
    b_count_events(malformed.common.events, O2aAddressResolve) == 3);
  let cap = b_run(b_two(mul), b_empty(), empty, 1,
    [|b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
      b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
      b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
      b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
      b_plan(0, Some(two), None())|]);
  b_ok("CANDIDATE_CAP", cap, cap.solver == O2bCandidateCap &
    cap.common.cells[3] == None());
  let nonmatching_cap = b_run(b_two(mul), b_empty(), empty, 1,
    b_plan(0, Some(two), Some(three)) ::
      b_irrelevant_plans(9, [||]));
  b_ok("NONMATCHING_NOT_COUNTED", nonmatching_cap, nonmatching_cap.solver == O2bCompleted &
    nonmatching_cap.common.status == O2aGeneratedHalted);

  let sixty_four = b_irrelevant_plans(64, [||]);
  let sixty_five = b_irrelevant_plans(65, [||]);
  let at_64 = b_run(b_two(mul), b_empty(), empty, 1, sixty_four);
  b_ok("TOTAL_64_NO_MATCH_PARITY", at_64, at_64.solver == O2bCompleted &
    at_64.common == baseline);
  let at_65 = b_run(b_two(mul), b_empty(), empty, 1, sixty_five);
  b_ok("TOTAL_65_LIMIT_AFTER_ADDRESSES", at_65, at_65.solver == O2bPlanListLimit &
    at_65.common.status == O2aRunning &
    at_65.common.image_tag == O2aDiagnosticPartial &
    b_count_events(at_65.common.events, O2aStepStart) == 1 &
    b_count_events(at_65.common.events, O2aAddressResolve) == 3 &
    b_count_events(at_65.common.events, O2bMulAdviceWrite) == 0 &
    at_65.common.cells[3] == None());
  let first_65 = b_run(b_two(Mul(0x0000000000000000,
    gpow(0x0000000000000004), gpow(0x0000000000000005))),
    b_empty(), empty, 1, sixty_five);
  let first_o2a = o2a_forward_run_parts(b_two(Mul(0x0000000000000000,
    gpow(0x0000000000000004), gpow(0x0000000000000005))),
    b_empty(), empty, sail_zeros(256), 1);
  b_ok("FIRST_BAD_ADDRESS_BEATS_65", first_65, first_65.solver == O2bCompleted &
    first_65.common == first_o2a);
  let second_65 = b_run(b_two(Mul(gpow(0x0000000000000003),
    0x0000000000000000, gpow(0x0000000000000005))),
    b_empty(), empty, 1, sixty_five);
  let second_o2a = o2a_forward_run_parts(b_two(Mul(gpow(0x0000000000000003),
    0x0000000000000000, gpow(0x0000000000000005))),
    b_empty(), empty, sail_zeros(256), 1);
  b_ok("SECOND_BAD_ADDRESS_BEATS_65", second_65, second_65.solver == O2bCompleted &
    second_65.common == second_o2a);
  let third_65 = b_run(b_two(Mul(gpow(0x0000000000000003),
    gpow(0x0000000000000004), 0x0000000000000000)),
    b_empty(), empty, 1, sixty_five);
  let third_o2a = o2a_forward_run_parts(b_two(Mul(gpow(0x0000000000000003),
    gpow(0x0000000000000004), 0x0000000000000000)),
    b_empty(), empty, sail_zeros(256), 1);
  b_ok("THIRD_BAD_ADDRESS_BEATS_65", third_65, third_65.solver == O2bCompleted &
    third_65.common == third_o2a);

  let nine_active = b_irrelevant_plans(55,
    [|b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
      b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
      b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
      b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
      b_plan(0, Some(two), None())|]);
  let nine_64 = b_run(b_two(mul), b_empty(), empty, 1, nine_active);
  b_ok("MATCHING_9_AT_TOTAL_64", nine_64, nine_64.solver == O2bCandidateCap &
    b_count_events(nine_64.common.events, O2bMulAdviceWrite) == 0);
  let nine_65 = b_run(b_two(mul), b_empty(), empty, 1,
    b_matching_plans(9, b_irrelevant_plans(56, [||])));
  b_ok("TOTAL_65_BEATS_MATCHING_9", nine_65, nine_65.solver == O2bPlanListLimit);
  let eight_active = b_irrelevant_plans(56,
    [|b_plan(0, Some(two), Some(three)), b_plan(0, Some(two), None()),
      b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
      b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
      b_plan(0, Some(two), None()), b_plan(0, Some(two), None())|]);
  let eight_64 = b_run(b_two(mul), b_empty(), empty, 1, eight_active);
  b_ok("MATCHING_8_AT_TOTAL_64", eight_64, eight_64.solver == O2bCompleted &
    eight_64.common.cells[5] == Some(six));
  let malformed_future = b_run(b_two(mul), b_empty(), empty, 1,
    [|b_plan(999, None(), None()), b_plan(0, Some(two), Some(three))|]);
  b_ok("FUTURE_MALFORMED_INERT", malformed_future, malformed_future.solver == O2bCompleted &
    malformed_future.common.cells[5] == Some(six));
  let cap_bad = b_run(b_two(mul), b_empty(), empty, 1,
    b_irrelevant_plans(54, b_plan(0, None(), None()) ::
      [|b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
        b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
        b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
        b_plan(0, Some(two), None()), b_plan(0, Some(two), None()),
        b_plan(0, Some(two), None())|]));
  b_ok("MATCHING_CAP_BEATS_MALFORMED", cap_bad, cap_bad.solver == O2bCandidateCap);

  let nonmul_program = b_two(Set(gpow(0x0000000000000008), sail_zeros(192)));
  let nonmul_65 = b_run(nonmul_program, b_empty(), empty, 1, sixty_five);
  let nonmul_o2a = o2a_forward_run_parts(nonmul_program, b_empty(), empty,
    sail_zeros(256), 1);
  b_ok("NONMUL_IGNORES_65", nonmul_65, nonmul_65.solver == O2bCompleted &
    nonmul_65.common == nonmul_o2a);
  let zero_fuel_65 = b_run(b_two(mul), b_empty(), empty, 0, sixty_five);
  let zero_fuel_o2a = o2a_forward_run_parts(b_two(mul), b_empty(), empty,
    sail_zeros(256), 0);
  b_ok("FUEL_IGNORES_65", zero_fuel_65, zero_fuel_65.solver == O2bCompleted &
    zero_fuel_65.common == zero_fuel_o2a);
  var public_bad = b_empty();
  public_bad[0] = Some(one);
  let public_65 = b_run(b_two(mul), public_bad, empty, 1, sixty_five);
  let public_o2a = o2a_forward_run_parts(b_two(mul), public_bad, empty,
    sail_zeros(256), 1);
  b_ok("PUBLIC_CONFLICT_IGNORES_65", public_65, public_65.solver == O2bCompleted &
    public_65.common == public_o2a);
  let invalid_advice : vector(1, o2a_advice) = vector_init(1,
    b_advice(65536, one));
  let advice_65 = b_run(b_two(mul), b_empty(), invalid_advice, 1, sixty_five);
  let advice_o2a = o2a_forward_run_parts(b_two(mul), b_empty(),
    invalid_advice, sail_zeros(256), 1);
  b_ok("ADVICE_FAILURE_IGNORES_65", advice_65, advice_65.solver == O2bCompleted &
    advice_65.common == advice_o2a);
  let sentinel_program : vector(1, instruction) = vector_init(1, mul);
  let sentinel_65 = b_run(sentinel_program, b_empty(), empty, 1, sixty_five);
  let sentinel_o2a = o2a_forward_run_parts(sentinel_program, b_empty(), empty,
    sail_zeros(256), 1);
  b_ok("SENTINEL_IGNORES_65", sentinel_65, sentinel_65.solver == O2bCompleted &
    sentinel_65.common == sentinel_o2a);

  let alias_cb = b_run(b_two(b_mul(3, 4, 4)), b_empty(), empty, 1,
    [|b_plan(0, Some(one), Some(three))|]);
  b_ok("ALIAS_C_B", alias_cb, alias_cb.solver == O2bCompleted &
    alias_cb.common.cells[4] == Some(three));
  let alias_cb_bad = b_run(b_two(b_mul(3, 4, 4)), b_empty(), empty, 1,
    [|b_plan(0, Some(two), Some(three))|]);
  b_ok("ALIAS_C_B_REJECT", alias_cb_bad, alias_cb_bad.solver == O2bCandidatesExhausted &
    alias_cb_bad.common.cells[3] == None());
  let zero_factor = b_run(b_two(mul), b_empty(), empty, 1,
    [|b_plan(0, Some(sail_zeros(192)), Some(three))|]);
  b_ok("ZERO_FACTOR_PRODUCT", zero_factor, zero_factor.solver == O2bCompleted &
    zero_factor.common.cells[5] == Some(sail_zeros(192)));
  let high = embed_k(0x8000000000000000);
  let high_product = emul(high, two);
  let high_run = b_run(b_two(mul), b_empty(), empty, 1,
    [|b_plan(0, Some(high), Some(two))|]);
  b_ok("HIGH_BIT_REDUCTION_PRODUCT", high_run, high_run.solver == O2bCompleted &
    high_run.common.cells[5] == Some(high_product));

  var loop_program = b_four();
  loop_program[0] = mul;
  loop_program[1] = Jump(gpow(0x0000000000000006),
    gpow(0x0000000000000007), gpow(0x0000000000000008));
  var loop_initial = b_empty();
  loop_initial[6] = Some(one);
  loop_initial[7] = Some(one);
  loop_initial[8] = Some(one);
  let repeated_pc = b_run(loop_program, loop_initial, empty, 3,
    [|b_plan(0, Some(two), Some(three)), b_plan(2, None(), None())|]);
  let first_choice : bool = match repeated_pc.choices {
    choice :: [||] => choice.step == 0 & choice.ordinal == 0,
    _ => false
  };
  b_ok("DYNAMIC_STEP_NOT_PC", repeated_pc, repeated_pc.solver == O2bMalformedPlan &
    repeated_pc.common.steps == 2 & first_choice &
    repeated_pc.common.cells[3] == Some(two) &
    repeated_pc.common.cells[5] == Some(six) &
    b_count_events(repeated_pc.common.events, O2aStepStart) == 3 &
    b_count_events(repeated_pc.common.events, O2aAddressResolve) == 9);

  var two_mul_program = b_four();
  two_mul_program[0] = b_mul(3, 4, 5);
  two_mul_program[1] = b_mul(6, 7, 8);
  var two_mul_initial = b_empty();
  two_mul_initial[8] = Some(six);
  let two_mul_plans : list(o2b_plan) = [|
    b_plan(0, Some(two), Some(three)),
    b_plan(1, Some(two), Some(two)),
    b_plan(1, Some(two), Some(three))
  |];
  let two_commits = b_run(two_mul_program, two_mul_initial, empty, 2,
    two_mul_plans);
  let ordered_success : bool = match two_commits.choices {
    first :: second :: [||] => first.step == 0 & first.ordinal == 0 &
      first.a_value == Some(two) & first.b_value == Some(three) &
      second.step == 1 & second.ordinal == 1 &
      second.a_value == Some(two) & second.b_value == Some(three),
    _ => false
  };
  b_ok("TWO_CHOICES_FORWARD_CHRONOLOGY", two_commits, two_commits.solver ==
    O2bCompleted & ordered_success & two_commits.common.steps == 2 &
    two_commits.common.cells[5] == Some(six) &
    two_commits.common.cells[8] == Some(six));

  two_mul_program[2] = b_mul(9, 10, 11);
  let later_diagnostic = b_run(two_mul_program, two_mul_initial, empty, 3,
    [|b_plan(0, Some(two), Some(three)),
      b_plan(1, Some(two), Some(two)),
      b_plan(1, Some(two), Some(three)),
      b_plan(2, None(), None())|]);
  let ordered_diagnostic : bool = match later_diagnostic.choices {
    first :: second :: [||] => first.step == 0 & first.ordinal == 0 &
      second.step == 1 & second.ordinal == 1 &
      first.a_value == Some(two) & second.b_value == Some(three),
    _ => false
  };
  b_ok("LATER_DIAGNOSTIC_PRESERVES_CHOICE_CHRONOLOGY", later_diagnostic,
    later_diagnostic.solver == O2bMalformedPlan &
    later_diagnostic.common.image_tag == O2aDiagnosticPartial &
    later_diagnostic.common.steps == 2 & ordered_diagnostic &
    later_diagnostic.common.cells[5] == Some(six) &
    later_diagnostic.common.cells[8] == Some(six) &
    later_diagnostic.common.cells[9] == None() &
    b_count_events(later_diagnostic.common.events, O2aStepStart) == 3 &
    b_count_events(later_diagnostic.common.events, O2aAddressResolve) == 9);

  let bad_shape : vector(3, instruction) = vector_init(3, mul);
  let shape_65 = b_run(bad_shape, b_empty(), empty, 1, sixty_five);
  let shape_o2a = o2a_forward_run_parts(bad_shape, b_empty(), empty,
    sail_zeros(256), 1);
  b_ok("SHAPE_FAILURE_IGNORES_65", shape_65,
    shape_65.solver == O2bCompleted & shape_65.common == shape_o2a &
    shape_65.common.status == O2aInvalidShape);

  var conflicting_advice : vector(2, o2a_advice) =
    vector_init(2, b_advice(3, two));
  conflicting_advice[1] = b_advice(3, three);
  let advice_conflict_65 = b_run(b_two(mul), b_empty(),
    conflicting_advice, 1, sixty_five);
  let advice_conflict_o2a = o2a_forward_run_parts(b_two(mul), b_empty(),
    conflicting_advice, sail_zeros(256), 1);
  b_ok("ORDERED_ADVICE_CONFLICT_IGNORES_65", advice_conflict_65,
    advice_conflict_65.solver == O2bCompleted &
    advice_conflict_65.common == advice_conflict_o2a &
    advice_conflict_65.common.status == O2aAdviceConflict &
    b_count_events(advice_conflict_65.common.events, O2aAdviceWrite) == 2);

  var fetch_program = b_four();
  fetch_program[0] = Jump(gpow(0x0000000000000006),
    gpow(0x0000000000000007), gpow(0x0000000000000008));
  var fetch_initial = b_empty();
  fetch_initial[6] = Some(one);
  fetch_initial[7] = Some(embed_k(gpow(0x0000000000000005)));
  fetch_initial[8] = Some(one);
  let fetch_65 = b_run(fetch_program, fetch_initial, empty, 2, sixty_five);
  let fetch_o2a = o2a_forward_run_parts(fetch_program, fetch_initial, empty,
    sail_zeros(256), 2);
  b_ok("FETCH_FAILURE_IGNORES_65", fetch_65,
    fetch_65.solver == O2bCompleted & fetch_65.common == fetch_o2a &
    fetch_65.common.status == O2aFetchFailure &
    b_count_events(fetch_65.common.events, O2aStepStart) == 1 &
    b_count_events(fetch_65.common.events, O2bMulAdviceWrite) == 0);

  var later_conflict_program = b_four();
  later_conflict_program[0] = mul;
  later_conflict_program[1] = Set(gpow(0x0000000000000003),
    embed_k(0x0000000000000007));
  let later_conflict = b_run(later_conflict_program, b_empty(), empty, 2,
    [|b_plan(0, Some(two), Some(three))|]);
  let kept_choice : bool = match later_conflict.choices {
    choice :: [||] => choice.step == 0 & choice.ordinal == 0 &
      choice.a_value == Some(two) & choice.b_value == Some(three),
    _ => false
  };
  b_ok("LATER_O2A_CONFLICT_PRESERVES_CHOICE", later_conflict,
    later_conflict.solver == O2bCompleted & kept_choice &
    later_conflict.common.status == O2aAssignmentConflict &
    later_conflict.common.image_tag == O2aDiagnosticPartial &
    later_conflict.common.cells[3] == Some(two) &
    later_conflict.common.cells[5] == Some(six))
}
