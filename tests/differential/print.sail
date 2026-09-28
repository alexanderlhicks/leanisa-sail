$include <string.sail>

// The adapter emits values calculated by the specification. Python supplies
// constants and parses the output; it does not evaluate VM instructions.
function differential_number(x : int) -> unit = print_endline(dec_str(x))

function differential_verdict(x : status) -> int = match x {
  Running => 0, Halted => 1, BadAccess => 2, BadValue => 3,
  BadInstance => 4, OutOfFuel => 5
}
