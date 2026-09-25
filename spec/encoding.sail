type bytecode_entry = vector(8, kword)

function encode(ins : instruction) -> bytecode_entry = {
  var row : bytecode_entry = vector_init(8, 0x0000000000000000);
  match ins {
    Xor(a, b, c) => { row[0] = 0x0000000000000001; row[1] = a; row[2] = b; row[3] = c },
    Mul(a, b, c) => { row[0] = 0x0000000000000002; row[1] = a; row[2] = b; row[3] = c },
    Set(o, k) => {
      row[0] = 0x0000000000000004; row[1] = o;
      row[2] = k[63..0]; row[3] = k[127..64]; row[4] = k[191..128]
    },
    Deref(o1, o2, o3, mode) => {
      row[0] = 0x0000000000000008; row[1] = o1; row[2] = o2; row[3] = o3;
      row[4] = if mode == Pc then 0x0000000000000001 else 0x0000000000000000;
      row[5] = if mode == Fp then 0x0000000000000001 else 0x0000000000000000
    },
    Jump(c, d, f) => { row[0] = 0x0000000000000010; row[1] = c; row[2] = d; row[3] = f },
    Blake2s(a, b, c, d, cv, out, md) => {
      row[0] = 0x0000000000000020; row[1] = a; row[2] = b; row[3] = c;
      row[4] = d; row[5] = cv; row[6] = out; row[7] = md
    }
  };
  row
}

function decode(row : bytecode_entry) -> option(instruction) = {
  let candidate : option(instruction) = match row[0] {
    0x0000000000000001 => Some(Xor(row[1], row[2], row[3])),
    0x0000000000000002 => Some(Mul(row[1], row[2], row[3])),
    0x0000000000000004 => Some(Set(row[1], row[4] @ row[3] @ row[2])),
    0x0000000000000008 => {
      if row[4] == 0x0000000000000000 & row[5] == 0x0000000000000000 then Some(Deref(row[1], row[2], row[3], Cell))
      else if row[4] == 0x0000000000000001 & row[5] == 0x0000000000000000 then Some(Deref(row[1], row[2], row[3], Pc))
      else if row[4] == 0x0000000000000000 & row[5] == 0x0000000000000001 then Some(Deref(row[1], row[2], row[3], Fp))
      else None()
    },
    0x0000000000000010 => Some(Jump(row[1], row[2], row[3])),
    0x0000000000000020 => Some(Blake2s(row[1], row[2], row[3], row[4], row[5], row[6], row[7])),
    _ => None()
  };
  match candidate {
    None() => None(),
    Some(ins) => {
      let encoded = encode(ins);
      foreach (i from 0 to 7) {
        if encoded[i] != row[i] then return None();
      };
      Some(ins)
    }
  }
}
