function expect_encoding(ins : instruction, expected : bytecode_entry) -> unit = {
  let actual = encode(ins);
  foreach (i from 0 to 7) {
    assert(actual[i] == expected[i], "Rust/Sail encoding")
  };
  match decode(actual) {
    None() => assert(false, "decode failed"),
    Some(decoded) => assert(decoded == ins, "decode encode roundtrip")
  }
}

val expect_step : forall 'n, 0 <= 'n <= 4294967296. (instruction, vector('n, eword), status) -> unit
function expect_step(ins, mem, verdict) = {
  let s : machine_state = struct { pc = 0x0000000000000001, fp = 0x0000000000000001 };
  let result = step(s, ins, mem);
  let index = build_address_index(length(mem));
  assert(step_indexed(s, ins, mem, index) == result, "indexed/reference step");
  assert(result.verdict == verdict, "step verdict");
  if verdict != Running then {
    assert(result.state.pc == s.pc & result.state.fp == s.fp, "failure preserves state")
  }
}

// Independent step probes: relation constraints, aliases, and complete state.
val probe_step : forall 'n, 0 <= 'n <= 4294967296.
  (machine_state, instruction, vector('n, eword), step_result, string) -> unit
function probe_step(state, ins, mem, expected, label) = {
  assert(step(state, ins, mem) == expected, label);
  assert(step_indexed(state, ins, mem, build_address_index(length(mem))) == expected,
    "independent indexed result")
}

function c1_probes() -> unit = {
  let one : kword = 0x0000000000000001;
  let two : kword = 0x0000000000000002;
  let four : kword = 0x0000000000000004;
  let eight : kword = 0x0000000000000008;
  let zero : eword = sail_zeros(192);
  let high : eword = 0x000000000000000100000000000000000000000000000000;
  let framed : machine_state = struct { pc = four, fp = two };
  let advanced : machine_state = struct { pc = eight, fp = two };
  var mem : vector(32, eword) = vector_init(32, zero);
  mem[2] = embed_k(eight);
  mem[3] = embed_k(four);
  probe_step(framed, Jump(one, two, four), mem,
    struct { state = advanced, verdict = Running }, "untaken framed jump preserves FP");
  foreach (i from 1 to 3) {
    mem[i] = mem[i] ^^ high;
    probe_step(framed, Jump(one, two, four), mem,
      struct { state = framed, verdict = BadValue }, "every jump operand has unconditional K guard");
    mem[i] = mem[i] ^^ high
  };
  mem[1] = embed_k(one);
  probe_step(framed, Jump(one, two, four), mem,
    struct { state = struct { pc = eight, fp = four }, verdict = Running },
    "taken framed jump installs both registers");
  probe_step(framed, Jump(one, one, one), mem,
    struct { state = struct { pc = one, fp = one }, verdict = Running },
    "fully aliased jump observes one consistent value");
  mem[1] = zero;
  probe_step(framed, Jump(one, gpow(0x000000000000001f), four), mem,
    struct { state = framed, verdict = BadAccess }, "untaken destination must still be in bounds");

  mem[1] = embed_k(eight);
  mem[2] = high;
  mem[3] = embed_k(0x0000000000000010);
  probe_step(framed, Deref(one, one, two, Pc), mem,
    struct { state = advanced, verdict = Running }, "Pc stores two advances, ignoring source value");
  probe_step(framed, Deref(one, one, gpow(0x000000000000001f), Pc), mem,
    struct { state = framed, verdict = BadAccess }, "Pc still checks unused source address");
  mem[3] = embed_k(two);
  probe_step(framed, Deref(one, one, two, Fp), mem,
    struct { state = advanced, verdict = Running }, "Fp stores current changed frame");
  probe_step(framed, Deref(one, one, gpow(0x000000000000001f), Fp), mem,
    struct { state = framed, verdict = BadAccess }, "Fp still checks unused source address");
  mem[3] = high;
  probe_step(framed, Deref(one, one, two, Cell), mem,
    struct { state = advanced, verdict = Running }, "Cell can relate non-base-field words");
  mem[3] = zero;
  probe_step(framed, Deref(one, one, two, Cell), mem,
    struct { state = framed, verdict = BadValue }, "unresolved deferred equality rejects final image");
  mem[1] = embed_k(two);
  probe_step(framed, Deref(one, one, one, Cell), mem,
    struct { state = advanced, verdict = Running }, "pointer source target alias in Cell mode");
  probe_step(framed, Deref(one, one, two, Fp), mem,
    struct { state = advanced, verdict = Running }, "pointer target alias in Fp mode");
  probe_step(framed, Deref(one, one, two, Pc), mem,
    struct { state = framed, verdict = BadValue }, "pointer target alias cannot overwrite observation");
  mem[1] = high;
  probe_step(framed, Deref(one, one, two, Cell), mem,
    struct { state = framed, verdict = BadAccess }, "access failure precedes pointer field failure");

  // All message operands and metadata alias zero. The raw top flag is then
  // exercised separately; the existing differential corpus checks compression.
  mem = vector_init(32, zero);
  let initial : machine_state = struct { pc = one, fp = one };
  let initial_next : machine_state = struct { pc = two, fp = one };
  let digest = blake_compress(sail_zeros(512), sail_zeros(256), sail_zeros(128));
  mem[4] = 0x0000000000000000 @ digest[127..0];
  mem[5] = 0x0000000000000000 @ digest[255..128];
  probe_step(initial, Blake2s(one, one, one, one, two, 0x0000000000000010, one), mem,
    struct { state = initial_next, verdict = Running }, "aliased message and metadata inputs");
  probe_step(initial, Blake2s(one, one, one, one, two, one, one), mem,
    struct { state = initial, verdict = BadValue }, "output overlapping observed zero cannot overwrite it");
  mem[0] = high;
  probe_step(initial, Blake2s(one, one, one, one, two, 0x0000000000000010, one), mem,
    struct { state = initial, verdict = BadValue }, "aliased chunk top lane must be zero");
  mem[0] = zero;
  mem[7] = 0x0000000000000000fedcba9876543210ffffffffffffffff;
  let flagged = blake_compress(sail_zeros(512), sail_zeros(256), mem[7][127..0]);
  assert(flagged != digest, "nonzero raw metadata changes this compression vector");
  mem[4] = 0x0000000000000000 @ flagged[127..0];
  mem[5] = 0x0000000000000000 @ flagged[255..128];
  probe_step(initial, Blake2s(one, one, one, one, two, 0x0000000000000010, 0x0000000000000080), mem,
    struct { state = initial_next, verdict = Running }, "raw metadata accepts arbitrary flags");
  probe_step(initial, Blake2s(one, one, one, one, gpow(0x000000000000001f), 0x0000000000000010, 0x0000000000000080), mem,
    struct { state = initial, verdict = BadAccess }, "second chaining-value cell must be in bounds");
  probe_step(initial, Blake2s(one, one, one, one, two, gpow(0x000000000000001f), 0x0000000000000080), mem,
    struct { state = initial, verdict = BadAccess }, "second output cell must be in bounds")
}


// Independent control-flow regressions. Every expected PC/FP is supplied
// directly; Rust cycle counts and eventual termination of loops are not used.
val c2_expect_run : forall 'p 'm, 'p >= 1 & 'm >= 2.
  (vector('p, instruction), vector('m, eword), nat, machine_state, status, string) -> unit
function c2_expect_run(program, mem, fuel, state, verdict, label) = {
  let expected : step_result = struct { state = state, verdict = verdict };
  let result = run(program, mem, sail_zeros(256), fuel);
  assert(result == expected, label);
  assert(run_indexed(program, mem, sail_zeros(256), fuel) == expected,
    "independent control-flow indexed result")
}

function c2_probes() -> unit = {
  let one : kword = 0x0000000000000001;
  let two : kword = 0x0000000000000002;
  let four : kword = 0x0000000000000004;
  let eight : kword = 0x0000000000000008;
  let sixteen : kword = 0x0000000000000010;
  let zero : eword = sail_zeros(192);
  let invalid : instruction = Set(0x0000000000000000, embed_k(one));
  var mem : vector(65536, eword) = vector_init(65536, zero);
  var program : vector(16, instruction) = vector_init(16, invalid);
  // First jump switches from frame 0 to frame 4 and skips an invalid instruction.
  mem[2] = embed_k(one);
  mem[3] = embed_k(four);
  mem[4] = embed_k(sixteen);
  program[0] = Jump(four, eight, sixteen);
  program[2] = Set(four, embed_k(0x0000000000000003));
  program[3] = Xor(four, eight, sixteen);
  program[4] = Mul(four, eight, 0x0000000000000020);
  mem[6] = embed_k(0x0000000000000003);
  mem[7] = embed_k(0x0000000000000005);
  mem[8] = embed_k(0x0000000000000006);
  mem[9] = embed_k(0x000000000000000f);
  // All three dereference modes execute under the changed frame.
  mem[10] = embed_k(0x0000000000001000); // pointer to cell 12
  mem[12] = mem[7];
  mem[13] = embed_k(0x0000000000000100); // pc=6 stores g^(6+2)
  mem[14] = embed_k(sixteen);
  program[5] = Deref(0x0000000000000040, one, eight, Cell);
  program[6] = Deref(0x0000000000000040, two, eight, Pc);
  program[7] = Deref(0x0000000000000040, four, eight, Fp);
  // Four unequal, independently addressed chunks; both CV halves also differ.
  mem[15] = 0x000000000000000000000000000000010000000000000002;
  mem[17] = 0x000000000000000000000000000000030000000000000004;
  mem[16] = 0x000000000000000000000000000000050000000000000006;
  mem[18] = 0x000000000000000000000000000000070000000000000008;
  mem[19] = 0x00000000000000000000000000000009000000000000000a;
  mem[20] = 0x0000000000000000000000000000000b000000000000000c;
  mem[23] = 0x00000000000000000123456789abcdeffedcba9876543210;
  let digest = blake_compress(mem[18][127..0] @ mem[16][127..0] @ mem[17][127..0] @ mem[15][127..0],
    mem[20][127..0] @ mem[19][127..0], mem[23][127..0]);
  mem[21] = 0x0000000000000000 @ digest[127..0];
  mem[22] = 0x0000000000000000 @ digest[255..128];
  program[8] = Blake2s(0x0000000000000800, 0x0000000000002000,
    0x0000000000001000, 0x0000000000004000, 0x0000000000008000,
    0x0000000000020000, 0x0000000000080000);
  // Restore the initial frame, skip two invalid cells, then jump to sentinel.
  mem[24] = embed_k(one);
  mem[25] = embed_k(0x0000000000001000);
  mem[26] = embed_k(one);
  program[9] = Jump(0x0000000000100000, 0x0000000000200000, 0x0000000000400000);
  mem[27] = embed_k(0x0000000000000007);
  program[12] = Set(0x0000000008000000, embed_k(0x0000000000000007));
  mem[28] = embed_k(one);
  mem[29] = embed_k(0x0000000000008000);
  mem[30] = embed_k(one);
  program[13] = Jump(0x0000000010000000, 0x0000000020000000, 0x0000000040000000);
  var pcs : vector(12, kword) = vector_init(12, one);
  pcs[1] = four;
  pcs[2] = eight;
  pcs[3] = sixteen;
  pcs[4] = 0x0000000000000020;
  pcs[5] = 0x0000000000000040;
  pcs[6] = 0x0000000000000080;
  pcs[7] = 0x0000000000000100;
  pcs[8] = 0x0000000000000200;
  pcs[9] = 0x0000000000001000;
  pcs[10] = 0x0000000000002000;
  pcs[11] = 0x0000000000008000;
  foreach (fuel from 0 to 14) {
    let count = if fuel < 11 then fuel else 11;
    let frame = if count > 0 & count < 9 then sixteen else one;
    let state : machine_state = struct { pc = pcs[count], fp = frame };
    c2_expect_run(program, mem, fuel, state, if fuel < 11 then OutOfFuel else Halted,
      "all-opcode mixed-frame exact prefix and terminal registers")
  };
  // Bad final FP is observed at exact fuel, before fetching the invalid sentinel.
  mem[30] = embed_k(sixteen);
  foreach (fuel from 11 to 13) {
    c2_expect_run(program, mem, fuel,
      struct { pc = 0x0000000000008000, fp = sixteen }, BadValue,
      "nonunit final frame with exact and surplus fuel")
  };
  mem[30] = embed_k(one);
  // A failed relation is not inspected until there is fuel to attempt that step.
  mem[8] = mem[8] ^^ embed_k(one);
  c2_expect_run(program, mem, 2, struct { pc = eight, fp = sixteen }, OutOfFuel,
    "fuel exhausted at failing XOR before relation check");
  c2_expect_run(program, mem, 3, struct { pc = eight, fp = sixteen }, BadValue,
    "failed XOR after valid prefix preserves both registers");
  mem[8] = mem[8] ^^ embed_k(one);
  // A valid JUMP may produce an invalid next fetch address.
  mem[3] = zero;
  c2_expect_run(program, mem, 1, struct { pc = 0x0000000000000000, fp = sixteen }, OutOfFuel,
    "fuel exhausted before invalid fetch");
  c2_expect_run(program, mem, 2, struct { pc = 0x0000000000000000, fp = sixteen }, BadAccess,
    "invalid fetch after successful jump preserves changed frame");
  mem[3] = embed_k(four);
  program[2] = invalid;
  c2_expect_run(program, mem, 1, struct { pc = four, fp = sixteen }, OutOfFuel,
    "fuel exhausted before invalid instruction access");
  c2_expect_run(program, mem, 2, struct { pc = four, fp = sixteen }, BadAccess,
    "invalid instruction access after valid prefix preserves registers");
  // A genuine self-loop has finite prefixes without any terminating extension.
  var loop : vector(2, instruction) = vector_init(2, invalid);
  loop[0] = Jump(four, four, four);
  foreach (fuel from 0 to 5) {
    c2_expect_run(loop, mem, fuel, struct { pc = one, fp = one }, OutOfFuel,
      "self-loop prefixes need no eventual halt")
  };
  // Instance binding precedes fuel and sentinel decisions, including zero steps.
  let singleton : vector(1, instruction) = vector_init(1, invalid);
  mem[0] = embed_k(one);
  c2_expect_run(singleton, mem, 0, struct { pc = one, fp = one }, BadInstance,
    "invalid singleton instance is rejected before halt and fuel")
}


// The typed Sail decoder accepts arbitrary 64-bit K encodings. These tests do
// not pass their raw operands through the Rust adapter's u32 offset conversion.
function e1_roundtrip(ins : instruction) -> unit = {
  let row = encode(ins);
  match decode(row) {
    None() => assert(false, "typed instruction encoding must decode"),
    Some(actual) => {
      assert(actual == ins, "full-width typed instruction roundtrip");
      assert(encode(actual) == row, "accepted row is exactly canonical")
    }
  }
}

function e1_unused(ins : instruction, first : range(0, 7)) -> unit = {
  var row = encode(ins);
  foreach (i from first to 7) {
    assert(row[i] == 0x0000000000000000, "every unused slot starts at zero");
    row[i] = 0x0000000000000001;
    assert(is_none(decode(row)), "each unused slot rejects a low nonzero bit");
    row[i] = 0x8000000000000000;
    assert(is_none(decode(row)), "each unused slot rejects a high nonzero bit");
    row[i] = 0x0000000000000000
  }
}

function e1_probes() -> unit = {
  let zero : kword = 0x0000000000000000;
  let one : kword = 0x0000000000000001;
  let high : kword = 0x8000000000000000;
  let max : kword = 0xffffffffffffffff;
  let wider_than_u32 : kword = 0x0000000100000000;
  let mixed : eword = 0xfedcba98765432100123456789abcdef8000000000000001;
  e1_roundtrip(Xor(zero, high, max));
  e1_roundtrip(Mul(max, wider_than_u32, zero));
  e1_roundtrip(Set(zero, sail_zeros(192)));
  e1_roundtrip(Set(max, 0xffffffffffffffffffffffffffffffffffffffffffffffff));
  e1_roundtrip(Set(high, mixed));
  e1_roundtrip(Deref(zero, max, wider_than_u32, Cell));
  e1_roundtrip(Deref(high, wider_than_u32, max, Pc));
  e1_roundtrip(Deref(max, zero, high, Fp));
  e1_roundtrip(Jump(wider_than_u32, max, zero));
  e1_roundtrip(Blake2s(zero, one, high, max, wider_than_u32,
    0xaaaaaaaaaaaaaaaa, 0x5555555555555555));
  // Every one of SET's 192 bit positions is packed into its independently
  // calculated limb and roundtrips, including all six limb-edge bits.
  foreach (bit from 0 to 191) {
    var immediate : eword = sail_zeros(192);
    immediate[bit] = bitone;
    var expected : bytecode_entry = vector_init(8, zero);
    expected[0] = 0x0000000000000004;
    expected[1] = max;
    var limb : kword = zero;
    if bit < 64 then {
      limb[bit] = bitone;
      expected[2] = limb
    } else if bit < 128 then {
      limb[bit - 64] = bitone;
      expected[3] = limb
    } else {
      limb[bit - 128] = bitone;
      expected[4] = limb
    };
    assert(encode(Set(max, immediate)) == expected, "SET every bit has the correct limb and position");
    e1_roundtrip(Set(max, immediate))
  };
  // Check the raw row entry point and exact low/middle/high SET limb order.
  var row : bytecode_entry = vector_init(8, zero);
  row[0] = 0x0000000000000004;
  row[1] = high;
  row[2] = 0x8000000000000001;
  row[3] = 0x0123456789abcdef;
  row[4] = 0xfedcba9876543210;
  match decode(row) {
    None() => assert(false, "raw full-width SET row must decode"),
    Some(ins) => assert(ins == Set(high, mixed), "raw SET row limb reassembly")
  };

  e1_unused(Xor(zero, high, max), 4);
  e1_unused(Mul(max, wider_than_u32, zero), 4);
  e1_unused(Set(high, mixed), 5);
  e1_unused(Deref(zero, max, high, Cell), 6);
  e1_unused(Deref(zero, max, high, Pc), 6);
  e1_unused(Deref(zero, max, high, Fp), 6);
  e1_unused(Jump(high, max, zero), 4);

  // Every non-Boolean flag bit must reject independently; only bit zero gives
  // a legal Pc/Fp flag. Setting both legal flags must still reject.
  foreach (bit from 0 to 63) {
    var flag : kword = zero;
    flag[bit] = bitone;
    row = encode(Deref(zero, max, high, Cell));
    row[4] = flag;
    assert(is_some(decode(row)) == (bit == 0), "Pc flag accepts exactly its Boolean bit");
    row[4] = zero;
    row[5] = flag;
    assert(is_some(decode(row)) == (bit == 0), "Fp flag accepts exactly its Boolean bit");
    row[4] = one;
    assert(is_none(decode(row)), "two flags or non-Boolean Fp flag must reject")
  };
  row = encode(Deref(zero, max, high, Cell));
  row[4] = max;
  assert(is_none(decode(row)), "all-ones flag is not Boolean");
  row[4] = zero;
  row[5] = max;
  assert(is_none(decode(row)), "all-ones frame flag is not Boolean");

  // Opcodes are precisely the six low singleton bits, not arbitrary masks or
  // truncated integer encodings. All-zero operands form legal typed rows.
  foreach (bit from 0 to 63) {
    row = vector_init(8, zero);
    var opcode : kword = zero;
    opcode[bit] = bitone;
    row[0] = opcode;
    assert(is_some(decode(row)) == (bit < 6), "every opcode bit checks full 64-bit dispatch")
  };
  row = vector_init(8, zero);
  assert(is_none(decode(row)), "zero opcode rejects");
  row[0] = 0x0000000000000003;
  assert(is_none(decode(row)), "combined opcode bits reject");
  row[0] = max;
  assert(is_none(decode(row)), "all-ones opcode rejects");
  row[0] = 0x0000000100000001;
  assert(is_none(decode(row)), "high opcode bits are not truncated")
}


// Independent literal values from carryless polynomial reduction; executable evidence only.
function field_loop_probes() -> unit = {
  assert(advance(0x0000000000000000) == 0x0000000000000000, "advance carry and mask boundary");
  assert(advance(0x0000000000000001) == 0x0000000000000002, "advance carry and mask boundary");
  assert(advance(0x4000000000000000) == 0x8000000000000000, "advance carry and mask boundary");
  assert(advance(0x8000000000000000) == 0x000000000000001b, "advance carry and mask boundary");
  assert(advance(0x8000000000000001) == 0x0000000000000019, "advance carry and mask boundary");
  assert(advance(0xffffffffffffffff) == 0xffffffffffffffe5, "advance carry and mask boundary");
  assert(advance(0x5555555555555555) == 0xaaaaaaaaaaaaaaaa, "advance carry and mask boundary");
  assert(advance(0xaaaaaaaaaaaaaaaa) == 0x555555555555554f, "advance carry and mask boundary");
  assert(kmul(0x0000000000000000, 0xffffffffffffffff) == 0x0000000000000000, "multiplication final-bit and update-order boundary");
  assert(kmul(0x0000000000000001, 0x8000000000000000) == 0x8000000000000000, "multiplication final-bit and update-order boundary");
  assert(kmul(0x8000000000000000, 0x0000000000000001) == 0x8000000000000000, "multiplication final-bit and update-order boundary");
  assert(kmul(0x8000000000000000, 0x0000000000000002) == 0x000000000000001b, "multiplication final-bit and update-order boundary");
  assert(kmul(0x8000000000000001, 0x0000000000000003) == 0x8000000000000018, "multiplication final-bit and update-order boundary");
  assert(kmul(0xffffffffffffffff, 0xffffffffffffffff) == 0x5555555555555513, "multiplication final-bit and update-order boundary");
  assert(kmul(0xffffffffffffffff, 0x8000000000000000) == 0x0000000000000065, "multiplication final-bit and update-order boundary");
  assert(kmul(0x0123456789abcdef, 0x8000000000000000) == 0x8c25d976268f73d1, "multiplication final-bit and update-order boundary");
  ()
}

// Independent carryless-product/long-reduction expected values.
// Typed Sail inputs are 64-bit words; the last two labels describe larger
// natural inputs reduced modulo 2^64 before these executable calls.
function power_loop_probes() -> unit = {
  assert(gpow(0x0000000000000000) == 0x0000000000000001, "gpow exact-order boundary for Nat 0");
  assert(gpow(0x0000000000000001) == 0x0000000000000002, "gpow exact-order boundary for Nat 1");
  assert(gpow(0x0000000000000002) == 0x0000000000000004, "gpow exact-order boundary for Nat 2");
  assert(gpow(0x000000000000003f) == 0x8000000000000000, "gpow exact-order boundary for Nat 63");
  assert(gpow(0x0000000000000040) == 0x000000000000001b, "gpow exact-order boundary for Nat 64");
  assert(gpow(0x8000000000000000) == 0xffffffff0000000a, "gpow exact-order boundary for Nat 9223372036854775808");
  assert(gpow(0xffffffffffffffff) == 0x0000000000000001, "gpow exact-order boundary for Nat 18446744073709551615");
  assert(gpow(0x0000ffff0000ffff) == 0x1c1e79669b95a7ce, "gpow exact-order boundary for Nat 281470681808895");
  assert(gpow(0x00000280fffffd7f) == 0x00f542601703f991, "gpow exact-order boundary for Nat 2753074036095");
  assert(gpow(0x0000000000000000) == 0x0000000000000001, "gpow exact-order boundary for Nat 18446744073709551616");
  assert(gpow(0x0000000000000001) == 0x0000000000000002, "gpow exact-order boundary for Nat 18446744073709551617");
  ()
}

function boundaries() -> unit = {
  power_loop_probes();
  field_loop_probes();
  e1_probes();
  c2_probes();
  c1_probes();
  assert(gpow(0xffffffffffffffff) == 0x0000000000000001, "generator order divides group size");
  assert(gpow(0x5555555555555555) != 0x0000000000000001, "generator factor 3");
  assert(gpow(0x3333333333333333) != 0x0000000000000001, "generator factor 5");
  assert(gpow(0x0f0f0f0f0f0f0f0f) != 0x0000000000000001, "generator factor 17");
  assert(gpow(0x00ff00ff00ff00ff) != 0x0000000000000001, "generator factor 257");
  assert(gpow(0x00663d80ff99c27f) != 0x0000000000000001, "generator factor 641");
  assert(gpow(0x0000ffff0000ffff) != 0x0000000000000001, "generator factor 65537");
  assert(gpow(0x00000280fffffd7f) != 0x0000000000000001, "generator factor 6700417");
  let one : kword = 0x0000000000000001;
  let two : kword = 0x0000000000000002;
  let four : kword = 0x0000000000000004;
  let eight : kword = 0x0000000000000008;
  let zero : eword = sail_zeros(192);
  let y : eword = 0x000000000000000000000000000000010000000000000000;
  var crossing : vector(128, eword) = vector_init(128, zero);
  crossing[64] = y;
  let before_reduction : machine_state = struct { pc = 0x8000000000000000, fp = one };
  let after_reduction = step(before_reduction, Set(0x000000000000001b, y), crossing);
  assert(after_reduction.verdict == Running & after_reduction.state.pc == 0x000000000000001b,
    "address indexing across polynomial reduction");
  var mem : vector(8, eword) = vector_init(8, zero);
  expect_step(Xor(one, two, four), mem, Running);
  expect_step(Mul(one, two, four), mem, Running);
  expect_step(Set(one, embed_k(two)), mem, BadValue);
  expect_step(Set(0x0000000000000000, zero), mem, BadAccess);
  expect_step(Set(gpow(0x0000000000000008), zero), mem, BadAccess);
  expect_step(Jump(one, two, four), mem, Running);
  mem[1] = y;
  expect_step(Jump(one, two, four), mem, BadValue);
  mem[1] = zero;
  mem[2] = y;
  expect_step(Jump(one, two, four), mem, BadValue);
  mem[2] = zero;
  mem[0] = y;
  expect_step(Jump(one, two, four), mem, BadValue);
  mem[0] = embed_k(four);
  expect_step(Deref(one, one, two, Cell), mem, Running);
  expect_step(Deref(one, one, two, Pc), mem, BadValue);
  mem[2] = embed_k(four);
  expect_step(Deref(one, one, two, Pc), mem, Running);
  expect_step(Deref(one, one, 0x0000000000000000, Pc), mem, BadAccess);
  mem[2] = embed_k(one);
  expect_step(Deref(one, one, two, Fp), mem, Running);
  mem[0] = y;
  expect_step(Deref(one, one, two, Cell), mem, BadAccess);
  mem[0] = y ^^ embed_k(four);
  expect_step(Deref(one, one, two, Cell), mem, BadValue);
  mem[0] = embed_k(one);
  mem[1] = embed_k(eight);
  mem[2] = embed_k(two);
  let initial : machine_state = struct { pc = one, fp = one };
  let jumped = step(initial, Jump(one, two, four), mem);
  assert(jumped.verdict == Running & jumped.state.pc == eight & jumped.state.fp == two, "taken jump registers");
  let framed : machine_state = struct { pc = one, fp = two };
  let relative = step(framed, Set(one, embed_k(eight)), mem);
  assert(relative.verdict == Running & relative.state.pc == two & relative.state.fp == two, "frame-relative access");

  var row = encode(Deref(one, two, four, Pc));
  assert(is_some(decode(row)), "canonical decode");
  row[5] = one;
  assert(is_none(decode(row)), "two deref flags");
  row[5] = 0x0000000000000000;
  row[4] = two;
  assert(is_none(decode(row)), "nonboolean deref flag");
  row = encode(Xor(one, two, four));
  row[7] = one;
  assert(is_none(decode(row)), "nonzero unused slot");
  row[0] = 0x0000000000000003;
  assert(is_none(decode(row)), "unknown opcode");

  var image : vector(65536, eword) = vector_init(65536, zero);
  var program : vector(2, instruction) = vector_init(2, Xor(one, one, one));
  let input : bits(256) = sail_zeros(256);
  assert(run(program, image, input, 0).verdict == OutOfFuel, "fuel zero");
  assert(run(program, image, input, 1).verdict == Halted, "one step halt");
  let singleton : vector(1, instruction) = vector_init(1, Set(one, y));
  assert(run(singleton, image, input, 0).verdict == Halted, "pre-fetch singleton halt");
  // SET/XOR composition: every fuel prefix has exact registers, and surplus
  // fuel must not execute the deliberately invalid sentinel instruction.
  var fragment : vector(4, instruction) = vector_init(4, Set(0x0000000000000000, y));
  fragment[0] = Set(four, embed_k(two));
  fragment[1] = Xor(four, one, four); // output aliases an input consistently
  fragment[2] = Xor(four, four, eight); // both inputs alias, fixing zero
  image[2] = embed_k(two);
  foreach (fuel from 0 to 5) {
    let result = run(fragment, image, input, fuel);
    let steps = if fuel < 3 then fuel else 3;
    assert(result.state.pc == gpow(get_slice_int(64, steps, 0)) & result.state.fp == one,
      "SET/XOR fuel-prefix registers");
    assert(result.verdict == (if fuel < 3 then OutOfFuel else Halted),
      "SET/XOR exact and surplus fuel");
    assert(run_indexed(fragment, image, input, fuel) == result,
      "SET/XOR indexed/reference fuel prefixes")
  };
  image[2] = zero;
  // Mixed SET/XOR/MUL composition, including extension reduction and a
  // consistent output alias. The malformed sentinel remains unexecuted.
  var arithmetic : vector(8, instruction) = vector_init(8, Set(0x0000000000000000, y));
  let y2 : eword = 0x000000000000000100000000000000000000000000000000;
  let sixteen : kword = 0x0000000000000010;
  let thirtytwo : kword = 0x0000000000000020;
  let sixtyfour : kword = 0x0000000000000040;
  arithmetic[0] = Set(four, y);
  arithmetic[1] = Set(eight, y2);
  arithmetic[2] = Mul(four, eight, sixteen);
  arithmetic[3] = Xor(sixteen, four, thirtytwo);
  arithmetic[4] = Mul(sixteen, thirtytwo, sixteen);
  arithmetic[5] = Set(sixtyfour, embed_k(one));
  arithmetic[6] = Mul(sixtyfour, sixtyfour, sixtyfour);
  image[2] = y;
  image[3] = y2;
  image[4] = y ^^ embed_k(one);
  image[5] = embed_k(one);
  image[6] = embed_k(one);
  foreach (fuel from 0 to 9) {
    let result = run(arithmetic, image, input, fuel);
    let steps = if fuel < 7 then fuel else 7;
    assert(result.state.pc == gpow(get_slice_int(64, steps, 0)) & result.state.fp == one,
      "SET/XOR/MUL fuel-prefix registers");
    assert(result.verdict == (if fuel < 7 then OutOfFuel else Halted),
      "SET/XOR/MUL exact and surplus fuel");
    assert(run_indexed(arithmetic, image, input, fuel) == result,
      "SET/XOR/MUL indexed/reference fuel prefixes")
  };
  image[4] = image[4] ^^ embed_k(one);
  let bad_product = run(arithmetic, image, input, 9);
  assert(bad_product.verdict == BadValue & bad_product.state.pc == four & bad_product.state.fp == one,
    "incorrect product rejects at MUL before advancing");
  assert(run_indexed(arithmetic, image, input, 9) == bad_product,
    "incorrect product indexed/reference failure state");
  foreach (i from 2 to 6) { image[i] = zero };
  image[0] = y;
  assert(run(singleton, image, input, 0).verdict == BadInstance,
    "public input binding precedes zero-step halt");
  assert(run(program, image, input, 1).verdict == BadInstance, "public input binding");
  image[0] = zero;
  image[2] = embed_k(one);
  image[3] = embed_k(two);
  image[4] = embed_k(two);
  program[0] = Jump(four, eight, 0x0000000000000010);
  assert(run(program, image, input, 1).verdict == BadValue, "final frame pointer");
  assert(run(program, image, input, 2).verdict == BadValue, "final frame with surplus fuel");
  image[3] = embed_k(one);
  image[4] = embed_k(one);
  assert(run(program, image, input, 3).verdict == OutOfFuel, "loop is not successful halt");
  image[3] = zero;
  assert(run(program, image, input, 2).verdict == BadAccess, "invalid taken pc");
  assert(run(program, mem, input, 1).verdict == BadInstance, "minimum memory size");
  let odd_program : vector(3, instruction) = vector_init(3, Xor(one, one, one));
  assert(run(odd_program, image, input, 1).verdict == BadInstance, "program power of two");
}
