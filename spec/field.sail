default Order dec
$include <prelude.sail>

type kword = bits(64)
type eword = bits(192)

infixl 6 ^^
overload operator ^^ = {xor_vec}

function kmul(a : kword, b : kword) -> kword = {
  var x = a;
  var y = b;
  var z : kword = 0x0000000000000000;
  foreach (i from 0 to 63) {
    if y[0] == bitone then z = z ^^ x;
    let carry = x[63];
    x = x[62..0] @ 0b0;
    if carry == bitone then x = x ^^ 0x000000000000001b;
    y = 0b0 @ y[63..1];
  };
  z
}

function gpow(n : bits(64)) -> kword = {
  var x : kword = 0x0000000000000002;
  var y = n;
  var z : kword = 0x0000000000000001;
  foreach (i from 0 to 63) {
    if y[0] == bitone then z = kmul(z, x);
    x = kmul(x, x);
    y = 0b0 @ y[63..1];
  };
  z
}

function emul(a : eword, b : eword) -> eword = {
  let a0 = a[63..0];
  let a1 = a[127..64];
  let a2 = a[191..128];
  let b0 = b[63..0];
  let b1 = b[127..64];
  let b2 = b[191..128];
  let p0 = kmul(a0, b0);
  let p1 = kmul(a0, b1) ^^ kmul(a1, b0);
  let p2 = kmul(a0, b2) ^^ kmul(a1, b1) ^^ kmul(a2, b0);
  let p3 = kmul(a1, b2) ^^ kmul(a2, b1);
  let p4 = kmul(a2, b2);
  (p2 ^^ p4) @ (p1 ^^ p3 ^^ p4) @ (p0 ^^ p3)
}

function in_k(x : eword) -> bool = x[191..64] == 0x00000000000000000000000000000000
function in_chunk(x : eword) -> bool = x[191..128] == 0x0000000000000000
function embed_k(x : kword) -> eword = 0x00000000000000000000000000000000 @ x
