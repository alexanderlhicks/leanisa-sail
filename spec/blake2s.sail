type u32 = bits(32)
type blake_state = vector(16, u32)

function rotr32(x : u32, n : range(1, 31)) -> u32 =
  sail_shiftright(x, n) ^^ sail_shiftleft(x, 32 - n)

function blake_g(v0 : blake_state, a : range(0, 15), b : range(0, 15),
                 c : range(0, 15), d : range(0, 15), x : u32, y : u32) -> blake_state = {
  var v = v0;
  v[a] = v[a] + v[b] + x;
  v[d] = rotr32(v[d] ^^ v[a], 16);
  v[c] = v[c] + v[d];
  v[b] = rotr32(v[b] ^^ v[c], 12);
  v[a] = v[a] + v[b] + y;
  v[d] = rotr32(v[d] ^^ v[a], 8);
  v[c] = v[c] + v[d];
  v[b] = rotr32(v[b] ^^ v[c], 7);
  v
}

function blake_iv(i : range(0, 7)) -> u32 = match i {
  0 => 0x6a09e667, 1 => 0xbb67ae85, 2 => 0x3c6ef372, 3 => 0xa54ff53a,
  4 => 0x510e527f, 5 => 0x9b05688c, 6 => 0x1f83d9ab, _ => 0x5be0cd19
}

function sigma(r : range(0, 9), i : range(0, 15)) -> range(0, 15) = {
  let packed : bits(64) = match r {
    0 => 0xfedcba9876543210,
    1 => 0x357b20c16df984ae,
    2 => 0x491763eadf250c8b,
    3 => 0x8f04a562ebcd1397,
    4 => 0xd386cb1efa427509,
    5 => 0x91ef57d438b0a6c2,
    6 => 0xb8293670a4def15c,
    7 => 0xa2684f05931ce7bd,
    8 => 0x5a417d2c803b9ef6,
    _ => 0x0dc3e9bf5167482a
  };
  let shifted = sail_shiftright(packed, 4 * i);
  unsigned(shifted[3..0])
}

function blake_compress(message : bits(512), cv : bits(256), md : bits(128)) -> bits(256) = {
  var m : blake_state = vector_init(16, 0x00000000);
  var v : blake_state = vector_init(16, 0x00000000);
  foreach (i from 0 to 15) {
    m[i] = message[32 * i + 31 .. 32 * i];
  };
  foreach (i from 0 to 7) {
    v[i] = cv[32 * i + 31 .. 32 * i];
    v[i + 8] = blake_iv(i);
  };
  foreach (i from 0 to 3) {
    v[i + 12] = v[i + 12] ^^ md[32 * i + 31 .. 32 * i];
  };
  foreach (r from 0 to 9) {
    v = blake_g(v, 0, 4, 8, 12, m[sigma(r, 0)], m[sigma(r, 1)]);
    v = blake_g(v, 1, 5, 9, 13, m[sigma(r, 2)], m[sigma(r, 3)]);
    v = blake_g(v, 2, 6, 10, 14, m[sigma(r, 4)], m[sigma(r, 5)]);
    v = blake_g(v, 3, 7, 11, 15, m[sigma(r, 6)], m[sigma(r, 7)]);
    v = blake_g(v, 0, 5, 10, 15, m[sigma(r, 8)], m[sigma(r, 9)]);
    v = blake_g(v, 1, 6, 11, 12, m[sigma(r, 10)], m[sigma(r, 11)]);
    v = blake_g(v, 2, 7, 8, 13, m[sigma(r, 12)], m[sigma(r, 13)]);
    v = blake_g(v, 3, 4, 9, 14, m[sigma(r, 14)], m[sigma(r, 15)]);
  };
  var result : bits(256) = sail_zeros(256);
  foreach (i from 0 to 7) {
    result[32 * i + 31 .. 32 * i] = cv[32 * i + 31 .. 32 * i] ^^ v[i] ^^ v[i + 8];
  };
  result
}
