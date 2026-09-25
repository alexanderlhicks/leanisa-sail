// Complete O2b envelope: solver status, ordered committed choices, and the
// canonical complete O2a common result (all cells, pairs, events and checker).
function o2b_solver_number(x : o2b_solver_status) -> int = match x {
  O2bCompleted => 0, O2bCandidatesExhausted => 1,
  O2bMalformedPlan => 2, O2bCandidateCap => 3,
  O2bPlanListLimit => 4, O2bInternal => 5
}

function o2b_print_option(x : option(eword)) -> unit = match x {
  None() => print_endline("NONE"),
  Some(value) => { print_endline("SOME"); o2a_print_word(value) }
}

val o2b_print_choices : list(o2b_choice) -> unit
function o2b_print_choices(choices) = match choices {
  [||] => print_endline("END_CHOICES"),
  choice :: rest => {
    print_endline("CHOICE");
    o2a_print_nat(choice.step);
    o2a_print_nat(choice.ordinal);
    o2b_print_option(choice.a_value);
    o2b_print_option(choice.b_value);
    o2b_print_choices(rest)
  }
}

val o2b_choice_count : list(o2b_choice) -> nat
function o2b_choice_count(choices) = match choices {
  [||] => 0,
  _ :: rest => 1 + o2b_choice_count(rest)
}

val o2b_print_result : forall 'm, 'm >= 2. o2b_result('m) -> unit
function o2b_print_result(result) = {
  print_endline("BEGIN_O2b_ENVELOPE");
  o2a_print_int(o2b_solver_number(result.solver));
  o2a_print_nat(o2b_choice_count(result.choices));
  o2b_print_choices(result.choices);
  o2a_print_result(result.common);
  print_endline("END_O2b_ENVELOPE")
}
