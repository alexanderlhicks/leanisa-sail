$include <string.sail>

// Bounded pair-insertion probe.  It exercises the runner's sparse component
// path without serializing a dense image or calling the immutable checker.
function scale_work() -> o2a_work(65536) = struct {
  registers = struct { pc = 0x0000000000000001,
    fp = 0x0000000000000001 },
  cells = vector_init(65536, None()),
  origins = vector_init(65536, O2aUnknown),
  pending = [||], events = [||], components = None(),
  current_opcode = O2aNoOpcode, status = O2aRunning,
  phase = O2aInputPhase, failing_index = 0, failing_other = 0,
  pending_reason = O2aNoPendingIssue, steps = 0
}

function main() -> unit = {
  var w = scale_work();
  foreach (i from 3 to 1002) {
    w = o2a_pending(w, i, i + 1);
    assert(w.status == O2aRunning, "scale 1000 pair insertion")
  };
  match (o2s_root_of(w, 3), o2s_root_of(w, 1003)) {
    (Some(a), Some(b)) => assert(a.key == b.key & a.entry.size == 1001,
      "scale 1000 component"),
    _ => assert(false, "scale 1000 missing root")
  };
  print_endline("SCALE_1000_OK");
  foreach (i from 1003 to 4002) {
    w = o2a_pending(w, i, i + 1);
    assert(w.status == O2aRunning, "scale 4000 pair insertion")
  };
  match (o2s_root_of(w, 3), o2s_root_of(w, 4003)) {
    (Some(a), Some(b)) => assert(a.key == b.key & a.entry.size == 4001,
      "scale 4000 component"),
    _ => assert(false, "scale 4000 missing root")
  };
  print_endline("SCALE_4000_OK")
}
