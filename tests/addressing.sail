val checked_run : forall 'p 'm, 'p >= 1 & 'm >= 2.
  (vector('p, instruction), vector('m, eword), bits(256), nat) -> step_result
function checked_run(program, mem, public_input, fuel) = {
  let result = run_indexed(program, mem, public_input, fuel);
  assert(result == run(program, mem, public_input, fuel), "indexed/reference run");
  result
}

function address_tests() -> unit = {
  let zero : kword = 0x0000000000000000;
  let one : kword = 0x0000000000000001;
  let empty = build_address_index(0);
  assert(is_none(lookup_address(empty, one)), "empty address index");
  let singleton = build_address_index(1);
  assert(lookup_address(singleton, one) == Some(0), "singleton address index");
  assert(is_none(lookup_address(singleton, 0x0000000000000002)), "singleton miss");
  let odd = build_address_index(3);
  assert(lookup_address(odd, 0x0000000000000004) == Some(2), "non-power-of-two index size");
  assert(is_none(lookup_address(odd, 0x0000000000000008)), "non-power-of-two miss");
  let occupied : address_entry = struct { address = one, offset = 0 };
  let full : vector(4, address_entry) = vector_init(4, occupied);
  assert(is_none(lookup_address(full, 0x0000000000000002)), "full table miss terminates");

  let small = build_address_index(128);
  var mem : vector(128, eword) = vector_init(128, sail_zeros(192));
  var program : vector(128, instruction) = vector_init(128, Set(one, sail_zeros(192)));
  foreach (i from 0 to 127) {
    mem[i] = embed_k(get_slice_int(64, i + 1, 0));
    program[i] = Set(one, mem[i]);
  };
  var address = one;
  foreach (i from 0 to 127) {
    assert(lookup_address(small, address) == Some(i), "every indexed address resolves, including collisions");
    assert(read_memory_indexed(mem, small, address) == read_memory(mem, address), "indexed/reference memory");
    assert(fetch_indexed(program, small, address) == fetch(program, address), "indexed/reference fetch");
    address = advance(address);
  };
  let outside = address;
  assert(is_none(lookup_address(small, outside)), "first address outside index");
  assert(is_none(lookup_address(small, zero)), "zero address rejected");
  assert(read_memory_indexed(mem, small, outside) == read_memory(mem, outside), "invalid memory address");
  assert(fetch_indexed(program, small, outside) == fetch(program, outside), "invalid program address");

  let index = build_address_index(65536);
  var image : vector(65536, eword) = vector_init(65536, sail_zeros(192));
  let positions : vector(8, bits(64)) = [
    0x000000000000ffff, 0x0000000000008000, 0x0000000000007fff, 0x0000000000000080,
    0x000000000000007f, 0x0000000000000040, 0x000000000000003f, 0x0000000000000000
  ];
  foreach (j from 0 to 7) {
    let offset = unsigned(positions[j]);
    if offset < 65536 then image[offset] = embed_k(positions[j]);
  };
  foreach (j from 0 to 7) {
    let exponent = positions[j];
    let address = gpow(exponent);
    assert(lookup_address(index, address) == Some(unsigned(exponent[31..0])), "large index boundary");
    assert(read_memory_indexed(image, index, address) == read_memory(image, address), "large indexed/reference memory");
  };
  let last = gpow(0x000000000000ffff);
  assert(is_none(lookup_address(index, advance(last))), "large index upper bound");
  assert(not_bool(read_memory_indexed(mem, index, last).valid), "memory bound independent of index bound");
  assert(is_none(fetch_indexed(program, index, last)), "program bound independent of index bound");
  assert(read_memory_indexed(mem, empty, one) == read_memory(mem, one), "empty index reference fallback");

  let state : machine_state = struct { pc = 0x8000000000000000, fp = 0x000000000000001b };
  let ins = Set(one, mem[64]);
  assert(step_indexed(state, ins, mem, small) == step(state, ins, mem), "indexed frame and pc cross reduction");

  var short_program : vector(2, instruction) = vector_init(2, Set(last, embed_k(0x000000000000ffff)));
  image[0] = sail_zeros(192);
  assert(checked_run(short_program, image, sail_zeros(256), 1).verdict == Halted, "runner uses last memory cell");
  short_program[0] = Set(advance(last), sail_zeros(192));
  assert(checked_run(short_program, image, sail_zeros(256), 1).verdict == BadAccess, "runner rejects memory upper bound");
  assert(checked_run(short_program, image, sail_zeros(256), 0).verdict == OutOfFuel, "indexed runner zero fuel");
  let singleton_program : vector(1, instruction) = vector_init(1, Set(zero, sail_zeros(192)));
  assert(checked_run(singleton_program, image, sail_zeros(256), 0).verdict == Halted, "singleton skips index construction");

  var large_program : vector(131072, instruction) = vector_init(131072, Set(one, sail_zeros(192)));
  large_program[0] = Jump(0x0000000000000004, 0x0000000000000008, 0x0000000000000010);
  image[2] = embed_k(one);
  image[3] = embed_k(gpow(0x000000000001fffe));
  image[4] = embed_k(one);
  assert(checked_run(large_program, image, sail_zeros(256), 2).verdict == Halted,
    "shared index covers program larger than memory");
}
