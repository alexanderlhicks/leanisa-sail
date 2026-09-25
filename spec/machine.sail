$include <generic_equality.sail>

enum deref_mode = Cell | Pc | Fp

union instruction = {
  Xor : (kword, kword, kword),
  Mul : (kword, kword, kword),
  Set : (kword, eword),
  Deref : (kword, kword, kword, deref_mode),
  Jump : (kword, kword, kword),
  Blake2s : (kword, kword, kword, kword, kword, kword, kword)
}

struct machine_state = { pc : kword, fp : kword }
enum status = Running | Halted | BadAccess | BadValue | BadInstance | OutOfFuel
struct step_result = { state : machine_state, verdict : status }
struct memory_read = { value : eword, valid : bool }

function advance(a : kword) -> kword = {
  let shifted = a[62..0] @ 0b0;
  if a[63] == bitone then shifted ^^ 0x000000000000001b else shifted
}

type cell_index = range(0, 4294967295)
type address_slot_index = range(0, 8589934591)
struct address_entry = { address : kword, offset : cell_index }

// Open addressing with linear probing. Zero is never a generator power.
val address_slot : forall 'n, 0 <= 'n <= 8589934592.
  (vector('n, address_entry), kword) -> option(address_slot_index)
function address_slot(index, address) = {
  if length(index) == 0 then return None();
  let mixed = address ^^ (address[16..0] @ address[63..17]) ^^ (address[40..0] @ address[63..41]);
  let initial = tmod_int(unsigned(mixed), length(index));
  var slot : address_slot_index = if initial < length(index) then initial else 0;
  foreach (probe from 0 to length(index) - 1) {
    let position = slot;
    if position < length(index) then {
      let entry = index[position];
      if entry.address == 0x0000000000000000 | entry.address == address then return Some(position);
    };
    slot = if position + 1 < length(index) then position + 1 else 0;
  };
  None()
}

val build_address_index : forall 'n, 0 <= 'n <= 4294967296. int('n) -> vector(2 * 'n, address_entry)
function build_address_index(size) = {
  let empty : address_entry = struct { address = 0x0000000000000000, offset = 0 };
  var index = vector_init(2 * size, empty);
  var address : kword = 0x0000000000000001;
  foreach (i from 0 to size - 1) {
    match address_slot(index, address) {
      Some(slot) => if slot < length(index) then
        index[slot] = struct { address = address, offset = i },
      None() => ()
    };
    address = advance(address);
  };
  index
}

val lookup_address : forall 'n, 0 <= 'n <= 8589934592.
  (vector('n, address_entry), kword) -> option(cell_index)
function lookup_address(index, address) = {
  if address == 0x0000000000000000 then return None();
  match address_slot(index, address) {
    Some(slot) => {
      if slot < length(index) then {
        let entry = index[slot];
        if entry.address == address then return Some(entry.offset);
      };
      None()
    },
    None() => None()
  }
}

val read_memory : forall 'n, 'n >= 0. (vector('n, eword), kword) -> memory_read
function read_memory(mem, address) = {
  var a : kword = 0x0000000000000001;
  foreach (i from 0 to length(mem) - 1) {
    if a == address then return struct { value = mem[i], valid = true };
    a = advance(a);
  };
  struct { value = sail_zeros(192), valid = false }
}

val read_memory_indexed : forall 'n 'i, 'n >= 0 & 0 <= 'i <= 8589934592.
  (vector('n, eword), vector('i, address_entry), kword) -> memory_read
function read_memory_indexed(mem, index, address) = {
  if length(index) == 0 then return read_memory(mem, address);
  match lookup_address(index, address) {
    Some(offset) => if offset < length(mem) then return struct { value = mem[offset], valid = true },
    None() => ()
  };
  struct { value = sail_zeros(192), valid = false }
}

val step_indexed : forall 'n 'i, 'n >= 0 & 0 <= 'i <= 8589934592.
  (machine_state, instruction, vector('n, eword), vector('i, address_entry)) -> step_result
function step_indexed(s, ins, mem, index) = {
  var next : machine_state = struct { pc = advance(s.pc), fp = s.fp };
  var accesses_ok : bool = true;
  var relation_ok : bool = false;
  match ins {
    Xor(a, b, c) => {
      let va = read_memory_indexed(mem, index, kmul(s.fp, a));
      let vb = read_memory_indexed(mem, index, kmul(s.fp, b));
      let vc = read_memory_indexed(mem, index, kmul(s.fp, c));
      accesses_ok = va.valid & vb.valid & vc.valid;
      relation_ok = vc.value == (va.value ^^ vb.value);
    },
    Mul(a, b, c) => {
      let va = read_memory_indexed(mem, index, kmul(s.fp, a));
      let vb = read_memory_indexed(mem, index, kmul(s.fp, b));
      let vc = read_memory_indexed(mem, index, kmul(s.fp, c));
      accesses_ok = va.valid & vb.valid & vc.valid;
      relation_ok = vc.value == emul(va.value, vb.value);
    },
    Set(o, k) => {
      let v = read_memory_indexed(mem, index, kmul(s.fp, o));
      accesses_ok = v.valid;
      relation_ok = v.value == k;
    },
    Deref(o1, o2, o3, mode) => {
      let pointer = read_memory_indexed(mem, index, kmul(s.fp, o1));
      let source = read_memory_indexed(mem, index, kmul(s.fp, o3));
      let target = read_memory_indexed(mem, index, kmul(pointer.value[63..0], o2));
      let expected : eword = match mode {
        Cell => source.value,
        Pc => embed_k(advance(advance(s.pc))),
        Fp => embed_k(s.fp)
      };
      accesses_ok = pointer.valid & source.valid & target.valid;
      relation_ok = in_k(pointer.value) & target.value == expected;
    },
    Jump(oc, od, ofp) => {
      let c = read_memory_indexed(mem, index, kmul(s.fp, oc));
      let d = read_memory_indexed(mem, index, kmul(s.fp, od));
      let f = read_memory_indexed(mem, index, kmul(s.fp, ofp));
      accesses_ok = c.valid & d.valid & f.valid;
      relation_ok = in_k(c.value) & in_k(d.value) & in_k(f.value);
      if c.value[63..0] != 0x0000000000000000 then
        next = struct { pc = d.value[63..0], fp = f.value[63..0] };
    },
    Blake2s(o0, o1, o2, o3, ocv, oout, omd) => {
      let m0 = read_memory_indexed(mem, index, kmul(s.fp, o0));
      let m1 = read_memory_indexed(mem, index, kmul(s.fp, o1));
      let m2 = read_memory_indexed(mem, index, kmul(s.fp, o2));
      let m3 = read_memory_indexed(mem, index, kmul(s.fp, o3));
      let cv0 = read_memory_indexed(mem, index, kmul(s.fp, ocv));
      let cv1 = read_memory_indexed(mem, index, advance(kmul(s.fp, ocv)));
      let out0 = read_memory_indexed(mem, index, kmul(s.fp, oout));
      let out1 = read_memory_indexed(mem, index, advance(kmul(s.fp, oout)));
      let md = read_memory_indexed(mem, index, kmul(s.fp, omd));
      let message = m3.value[127..0] @ m2.value[127..0] @ m1.value[127..0] @ m0.value[127..0];
      let cv = cv1.value[127..0] @ cv0.value[127..0];
      let result = blake_compress(message, cv, md.value[127..0]);
      accesses_ok = m0.valid & m1.valid & m2.valid & m3.valid & cv0.valid & cv1.valid & out0.valid & out1.valid & md.valid;
      relation_ok = in_chunk(m0.value) & in_chunk(m1.value) & in_chunk(m2.value) & in_chunk(m3.value)
        & in_chunk(cv0.value) & in_chunk(cv1.value) & in_chunk(out0.value) & in_chunk(out1.value) & in_chunk(md.value)
        & out0.value[127..0] == result[127..0] & out1.value[127..0] == result[255..128];
    }
  };
  let verdict = if not_bool(accesses_ok) then BadAccess else if not_bool(relation_ok) then BadValue else Running;
  struct { state = if verdict == Running then next else s, verdict = verdict }
}

val step : forall 'n, 'n >= 0. (machine_state, instruction, vector('n, eword)) -> step_result
function step(s, ins, mem) = {
  let empty : address_entry = struct { address = 0x0000000000000000, offset = 0 };
  let index : vector(0, address_entry) = vector_init(0, empty);
  step_indexed(s, ins, mem, index)
}

function power_of_two(n : nat) -> bool = {
  var p : nat = 1;
  foreach (i from 0 to 32) {
    if n == p then return true;
    p = 2 * p;
  };
  false
}

val fetch : forall 'n, 'n >= 0. (vector('n, instruction), kword) -> option(instruction)
function fetch(program, address) = {
  var a : kword = 0x0000000000000001;
  foreach (i from 0 to length(program) - 1) {
    if a == address then return Some(program[i]);
    a = advance(a);
  };
  None()
}

val fetch_indexed : forall 'n 'i, 'n >= 0 & 0 <= 'i <= 8589934592.
  (vector('n, instruction), vector('i, address_entry), kword) -> option(instruction)
function fetch_indexed(program, index, address) = {
  match lookup_address(index, address) {
    Some(offset) => if offset < length(program) then return Some(program[offset]),
    None() => ()
  };
  None()
}

val run : forall 'p 'm, 'p >= 1 & 'm >= 2.
  (vector('p, instruction), vector('m, eword), bits(256), nat) -> step_result
function run(program, mem, public_input, fuel) = {
  var s : machine_state = struct { pc = 0x0000000000000001, fp = 0x0000000000000001 };
  if not_bool(power_of_two(length(program))) | not_bool(power_of_two(length(mem)))
      | length(mem) < 65536 | length(mem) > 4294967296 | length(program) > 4294967296
      | mem[0] != (0x0000000000000000 @ public_input[127..0])
      | mem[1] != (0x0000000000000000 @ public_input[255..128]) then
    return struct { state = s, verdict = BadInstance };
  let sentinel = gpow(get_slice_int(64, length(program) - 1, 0));
  foreach (i from 0 to fuel) {
    if s.pc == sentinel then return struct {
      state = s, verdict = if s.fp == 0x0000000000000001 then Halted else BadValue
    };
    if i == fuel then return struct { state = s, verdict = OutOfFuel };
    match fetch(program, s.pc) {
      None() => return struct { state = s, verdict = BadAccess },
      Some(ins) => {
        let result = step(s, ins, mem);
        if result.verdict != Running then return result;
        s = result.state;
      }
    };
  };
  struct { state = s, verdict = OutOfFuel }
}


val run_indexed : forall 'p 'm, 'p >= 1 & 'm >= 2.
  (vector('p, instruction), vector('m, eword), bits(256), nat) -> step_result
function run_indexed(program, mem, public_input, fuel) = {
  var s : machine_state = struct { pc = 0x0000000000000001, fp = 0x0000000000000001 };
  if not_bool(power_of_two(length(program))) | not_bool(power_of_two(length(mem)))
      | length(mem) < 65536 | length(mem) > 4294967296 | length(program) > 4294967296
      | mem[0] != (0x0000000000000000 @ public_input[127..0])
      | mem[1] != (0x0000000000000000 @ public_input[255..128]) then
    return struct { state = s, verdict = BadInstance };
  let sentinel = gpow(get_slice_int(64, length(program) - 1, 0));
  if s.pc == sentinel then return struct { state = s, verdict = Halted };
  if fuel == 0 then return struct { state = s, verdict = OutOfFuel };
  let size = if length(mem) >= length(program) then length(mem) else length(program);
  let index = build_address_index(size);
  foreach (i from 0 to fuel) {
    if s.pc == sentinel then return struct {
      state = s, verdict = if s.fp == 0x0000000000000001 then Halted else BadValue
    };
    if i == fuel then return struct { state = s, verdict = OutOfFuel };
    match fetch_indexed(program, index, s.pc) {
      None() => return struct { state = s, verdict = BadAccess },
      Some(ins) => {
        let result = step_indexed(s, ins, mem, index);
        if result.verdict != Running then return result;
        s = result.state;
      }
    };
  };
  struct { state = s, verdict = OutOfFuel }
}
