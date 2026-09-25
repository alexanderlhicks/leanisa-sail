// Sparse 32-bit component index.  Generated fixed-depth node functions are
// kept separate because Sail rejects recursive datatypes.
struct sp_entry = { parent : nat, size : nat, members : list(nat), fixed : bool, value : eword, min_index : nat }
struct sp_t0 = { value : sp_entry }
struct sp_t1 = { zero : list(sp_t0), one : list(sp_t0) }
struct sp_t2 = { zero : list(sp_t1), one : list(sp_t1) }
struct sp_t3 = { zero : list(sp_t2), one : list(sp_t2) }
struct sp_t4 = { zero : list(sp_t3), one : list(sp_t3) }
struct sp_t5 = { zero : list(sp_t4), one : list(sp_t4) }
struct sp_t6 = { zero : list(sp_t5), one : list(sp_t5) }
struct sp_t7 = { zero : list(sp_t6), one : list(sp_t6) }
struct sp_t8 = { zero : list(sp_t7), one : list(sp_t7) }
struct sp_t9 = { zero : list(sp_t8), one : list(sp_t8) }
struct sp_t10 = { zero : list(sp_t9), one : list(sp_t9) }
struct sp_t11 = { zero : list(sp_t10), one : list(sp_t10) }
struct sp_t12 = { zero : list(sp_t11), one : list(sp_t11) }
struct sp_t13 = { zero : list(sp_t12), one : list(sp_t12) }
struct sp_t14 = { zero : list(sp_t13), one : list(sp_t13) }
struct sp_t15 = { zero : list(sp_t14), one : list(sp_t14) }
struct sp_t16 = { zero : list(sp_t15), one : list(sp_t15) }
struct sp_t17 = { zero : list(sp_t16), one : list(sp_t16) }
struct sp_t18 = { zero : list(sp_t17), one : list(sp_t17) }
struct sp_t19 = { zero : list(sp_t18), one : list(sp_t18) }
struct sp_t20 = { zero : list(sp_t19), one : list(sp_t19) }
struct sp_t21 = { zero : list(sp_t20), one : list(sp_t20) }
struct sp_t22 = { zero : list(sp_t21), one : list(sp_t21) }
struct sp_t23 = { zero : list(sp_t22), one : list(sp_t22) }
struct sp_t24 = { zero : list(sp_t23), one : list(sp_t23) }
struct sp_t25 = { zero : list(sp_t24), one : list(sp_t24) }
struct sp_t26 = { zero : list(sp_t25), one : list(sp_t25) }
struct sp_t27 = { zero : list(sp_t26), one : list(sp_t26) }
struct sp_t28 = { zero : list(sp_t27), one : list(sp_t27) }
struct sp_t29 = { zero : list(sp_t28), one : list(sp_t28) }
struct sp_t30 = { zero : list(sp_t29), one : list(sp_t29) }
struct sp_t31 = { zero : list(sp_t30), one : list(sp_t30) }
struct sp_t32 = { zero : list(sp_t31), one : list(sp_t31) }
val sp_get_0 : (option(sp_t0), nat, nat) -> option(sp_entry)
function sp_get_0(tree, key, base) = match tree { None() => None(), Some(node) => Some(node.value) }
val sp_put_0 : (option(sp_t0), nat, nat, sp_entry) -> option(sp_t0)
function sp_put_0(tree, key, base, value) = Some(struct { value = value })
val sp_get_1 : (option(sp_t1), nat, nat) -> option(sp_entry)
function sp_get_1(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 1 then match node.zero { [||] => None(), child :: _ => sp_get_0(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_0(Some(child), key, base + 1) }
  }
}
val sp_put_1 : (option(sp_t1), nat, nat, sp_entry) -> option(sp_t1)
function sp_put_1(tree, key, base, value) = {
  var node : sp_t1 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 1 then {
    let old : option(sp_t0) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_0(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t0) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_0(old, key, base + 1, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_2 : (option(sp_t2), nat, nat) -> option(sp_entry)
function sp_get_2(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 2 then match node.zero { [||] => None(), child :: _ => sp_get_1(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_1(Some(child), key, base + 2) }
  }
}
val sp_put_2 : (option(sp_t2), nat, nat, sp_entry) -> option(sp_t2)
function sp_put_2(tree, key, base, value) = {
  var node : sp_t2 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 2 then {
    let old : option(sp_t1) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_1(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t1) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_1(old, key, base + 2, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_3 : (option(sp_t3), nat, nat) -> option(sp_entry)
function sp_get_3(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 4 then match node.zero { [||] => None(), child :: _ => sp_get_2(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_2(Some(child), key, base + 4) }
  }
}
val sp_put_3 : (option(sp_t3), nat, nat, sp_entry) -> option(sp_t3)
function sp_put_3(tree, key, base, value) = {
  var node : sp_t3 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 4 then {
    let old : option(sp_t2) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_2(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t2) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_2(old, key, base + 4, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_4 : (option(sp_t4), nat, nat) -> option(sp_entry)
function sp_get_4(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 8 then match node.zero { [||] => None(), child :: _ => sp_get_3(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_3(Some(child), key, base + 8) }
  }
}
val sp_put_4 : (option(sp_t4), nat, nat, sp_entry) -> option(sp_t4)
function sp_put_4(tree, key, base, value) = {
  var node : sp_t4 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 8 then {
    let old : option(sp_t3) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_3(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t3) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_3(old, key, base + 8, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_5 : (option(sp_t5), nat, nat) -> option(sp_entry)
function sp_get_5(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 16 then match node.zero { [||] => None(), child :: _ => sp_get_4(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_4(Some(child), key, base + 16) }
  }
}
val sp_put_5 : (option(sp_t5), nat, nat, sp_entry) -> option(sp_t5)
function sp_put_5(tree, key, base, value) = {
  var node : sp_t5 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 16 then {
    let old : option(sp_t4) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_4(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t4) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_4(old, key, base + 16, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_6 : (option(sp_t6), nat, nat) -> option(sp_entry)
function sp_get_6(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 32 then match node.zero { [||] => None(), child :: _ => sp_get_5(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_5(Some(child), key, base + 32) }
  }
}
val sp_put_6 : (option(sp_t6), nat, nat, sp_entry) -> option(sp_t6)
function sp_put_6(tree, key, base, value) = {
  var node : sp_t6 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 32 then {
    let old : option(sp_t5) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_5(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t5) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_5(old, key, base + 32, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_7 : (option(sp_t7), nat, nat) -> option(sp_entry)
function sp_get_7(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 64 then match node.zero { [||] => None(), child :: _ => sp_get_6(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_6(Some(child), key, base + 64) }
  }
}
val sp_put_7 : (option(sp_t7), nat, nat, sp_entry) -> option(sp_t7)
function sp_put_7(tree, key, base, value) = {
  var node : sp_t7 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 64 then {
    let old : option(sp_t6) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_6(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t6) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_6(old, key, base + 64, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_8 : (option(sp_t8), nat, nat) -> option(sp_entry)
function sp_get_8(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 128 then match node.zero { [||] => None(), child :: _ => sp_get_7(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_7(Some(child), key, base + 128) }
  }
}
val sp_put_8 : (option(sp_t8), nat, nat, sp_entry) -> option(sp_t8)
function sp_put_8(tree, key, base, value) = {
  var node : sp_t8 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 128 then {
    let old : option(sp_t7) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_7(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t7) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_7(old, key, base + 128, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_9 : (option(sp_t9), nat, nat) -> option(sp_entry)
function sp_get_9(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 256 then match node.zero { [||] => None(), child :: _ => sp_get_8(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_8(Some(child), key, base + 256) }
  }
}
val sp_put_9 : (option(sp_t9), nat, nat, sp_entry) -> option(sp_t9)
function sp_put_9(tree, key, base, value) = {
  var node : sp_t9 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 256 then {
    let old : option(sp_t8) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_8(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t8) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_8(old, key, base + 256, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_10 : (option(sp_t10), nat, nat) -> option(sp_entry)
function sp_get_10(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 512 then match node.zero { [||] => None(), child :: _ => sp_get_9(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_9(Some(child), key, base + 512) }
  }
}
val sp_put_10 : (option(sp_t10), nat, nat, sp_entry) -> option(sp_t10)
function sp_put_10(tree, key, base, value) = {
  var node : sp_t10 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 512 then {
    let old : option(sp_t9) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_9(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t9) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_9(old, key, base + 512, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_11 : (option(sp_t11), nat, nat) -> option(sp_entry)
function sp_get_11(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 1024 then match node.zero { [||] => None(), child :: _ => sp_get_10(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_10(Some(child), key, base + 1024) }
  }
}
val sp_put_11 : (option(sp_t11), nat, nat, sp_entry) -> option(sp_t11)
function sp_put_11(tree, key, base, value) = {
  var node : sp_t11 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 1024 then {
    let old : option(sp_t10) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_10(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t10) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_10(old, key, base + 1024, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_12 : (option(sp_t12), nat, nat) -> option(sp_entry)
function sp_get_12(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 2048 then match node.zero { [||] => None(), child :: _ => sp_get_11(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_11(Some(child), key, base + 2048) }
  }
}
val sp_put_12 : (option(sp_t12), nat, nat, sp_entry) -> option(sp_t12)
function sp_put_12(tree, key, base, value) = {
  var node : sp_t12 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 2048 then {
    let old : option(sp_t11) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_11(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t11) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_11(old, key, base + 2048, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_13 : (option(sp_t13), nat, nat) -> option(sp_entry)
function sp_get_13(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 4096 then match node.zero { [||] => None(), child :: _ => sp_get_12(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_12(Some(child), key, base + 4096) }
  }
}
val sp_put_13 : (option(sp_t13), nat, nat, sp_entry) -> option(sp_t13)
function sp_put_13(tree, key, base, value) = {
  var node : sp_t13 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 4096 then {
    let old : option(sp_t12) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_12(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t12) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_12(old, key, base + 4096, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_14 : (option(sp_t14), nat, nat) -> option(sp_entry)
function sp_get_14(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 8192 then match node.zero { [||] => None(), child :: _ => sp_get_13(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_13(Some(child), key, base + 8192) }
  }
}
val sp_put_14 : (option(sp_t14), nat, nat, sp_entry) -> option(sp_t14)
function sp_put_14(tree, key, base, value) = {
  var node : sp_t14 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 8192 then {
    let old : option(sp_t13) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_13(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t13) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_13(old, key, base + 8192, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_15 : (option(sp_t15), nat, nat) -> option(sp_entry)
function sp_get_15(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 16384 then match node.zero { [||] => None(), child :: _ => sp_get_14(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_14(Some(child), key, base + 16384) }
  }
}
val sp_put_15 : (option(sp_t15), nat, nat, sp_entry) -> option(sp_t15)
function sp_put_15(tree, key, base, value) = {
  var node : sp_t15 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 16384 then {
    let old : option(sp_t14) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_14(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t14) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_14(old, key, base + 16384, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_16 : (option(sp_t16), nat, nat) -> option(sp_entry)
function sp_get_16(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 32768 then match node.zero { [||] => None(), child :: _ => sp_get_15(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_15(Some(child), key, base + 32768) }
  }
}
val sp_put_16 : (option(sp_t16), nat, nat, sp_entry) -> option(sp_t16)
function sp_put_16(tree, key, base, value) = {
  var node : sp_t16 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 32768 then {
    let old : option(sp_t15) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_15(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t15) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_15(old, key, base + 32768, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_17 : (option(sp_t17), nat, nat) -> option(sp_entry)
function sp_get_17(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 65536 then match node.zero { [||] => None(), child :: _ => sp_get_16(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_16(Some(child), key, base + 65536) }
  }
}
val sp_put_17 : (option(sp_t17), nat, nat, sp_entry) -> option(sp_t17)
function sp_put_17(tree, key, base, value) = {
  var node : sp_t17 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 65536 then {
    let old : option(sp_t16) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_16(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t16) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_16(old, key, base + 65536, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_18 : (option(sp_t18), nat, nat) -> option(sp_entry)
function sp_get_18(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 131072 then match node.zero { [||] => None(), child :: _ => sp_get_17(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_17(Some(child), key, base + 131072) }
  }
}
val sp_put_18 : (option(sp_t18), nat, nat, sp_entry) -> option(sp_t18)
function sp_put_18(tree, key, base, value) = {
  var node : sp_t18 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 131072 then {
    let old : option(sp_t17) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_17(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t17) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_17(old, key, base + 131072, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_19 : (option(sp_t19), nat, nat) -> option(sp_entry)
function sp_get_19(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 262144 then match node.zero { [||] => None(), child :: _ => sp_get_18(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_18(Some(child), key, base + 262144) }
  }
}
val sp_put_19 : (option(sp_t19), nat, nat, sp_entry) -> option(sp_t19)
function sp_put_19(tree, key, base, value) = {
  var node : sp_t19 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 262144 then {
    let old : option(sp_t18) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_18(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t18) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_18(old, key, base + 262144, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_20 : (option(sp_t20), nat, nat) -> option(sp_entry)
function sp_get_20(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 524288 then match node.zero { [||] => None(), child :: _ => sp_get_19(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_19(Some(child), key, base + 524288) }
  }
}
val sp_put_20 : (option(sp_t20), nat, nat, sp_entry) -> option(sp_t20)
function sp_put_20(tree, key, base, value) = {
  var node : sp_t20 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 524288 then {
    let old : option(sp_t19) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_19(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t19) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_19(old, key, base + 524288, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_21 : (option(sp_t21), nat, nat) -> option(sp_entry)
function sp_get_21(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 1048576 then match node.zero { [||] => None(), child :: _ => sp_get_20(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_20(Some(child), key, base + 1048576) }
  }
}
val sp_put_21 : (option(sp_t21), nat, nat, sp_entry) -> option(sp_t21)
function sp_put_21(tree, key, base, value) = {
  var node : sp_t21 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 1048576 then {
    let old : option(sp_t20) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_20(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t20) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_20(old, key, base + 1048576, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_22 : (option(sp_t22), nat, nat) -> option(sp_entry)
function sp_get_22(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 2097152 then match node.zero { [||] => None(), child :: _ => sp_get_21(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_21(Some(child), key, base + 2097152) }
  }
}
val sp_put_22 : (option(sp_t22), nat, nat, sp_entry) -> option(sp_t22)
function sp_put_22(tree, key, base, value) = {
  var node : sp_t22 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 2097152 then {
    let old : option(sp_t21) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_21(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t21) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_21(old, key, base + 2097152, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_23 : (option(sp_t23), nat, nat) -> option(sp_entry)
function sp_get_23(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 4194304 then match node.zero { [||] => None(), child :: _ => sp_get_22(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_22(Some(child), key, base + 4194304) }
  }
}
val sp_put_23 : (option(sp_t23), nat, nat, sp_entry) -> option(sp_t23)
function sp_put_23(tree, key, base, value) = {
  var node : sp_t23 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 4194304 then {
    let old : option(sp_t22) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_22(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t22) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_22(old, key, base + 4194304, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_24 : (option(sp_t24), nat, nat) -> option(sp_entry)
function sp_get_24(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 8388608 then match node.zero { [||] => None(), child :: _ => sp_get_23(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_23(Some(child), key, base + 8388608) }
  }
}
val sp_put_24 : (option(sp_t24), nat, nat, sp_entry) -> option(sp_t24)
function sp_put_24(tree, key, base, value) = {
  var node : sp_t24 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 8388608 then {
    let old : option(sp_t23) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_23(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t23) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_23(old, key, base + 8388608, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_25 : (option(sp_t25), nat, nat) -> option(sp_entry)
function sp_get_25(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 16777216 then match node.zero { [||] => None(), child :: _ => sp_get_24(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_24(Some(child), key, base + 16777216) }
  }
}
val sp_put_25 : (option(sp_t25), nat, nat, sp_entry) -> option(sp_t25)
function sp_put_25(tree, key, base, value) = {
  var node : sp_t25 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 16777216 then {
    let old : option(sp_t24) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_24(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t24) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_24(old, key, base + 16777216, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_26 : (option(sp_t26), nat, nat) -> option(sp_entry)
function sp_get_26(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 33554432 then match node.zero { [||] => None(), child :: _ => sp_get_25(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_25(Some(child), key, base + 33554432) }
  }
}
val sp_put_26 : (option(sp_t26), nat, nat, sp_entry) -> option(sp_t26)
function sp_put_26(tree, key, base, value) = {
  var node : sp_t26 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 33554432 then {
    let old : option(sp_t25) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_25(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t25) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_25(old, key, base + 33554432, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_27 : (option(sp_t27), nat, nat) -> option(sp_entry)
function sp_get_27(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 67108864 then match node.zero { [||] => None(), child :: _ => sp_get_26(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_26(Some(child), key, base + 67108864) }
  }
}
val sp_put_27 : (option(sp_t27), nat, nat, sp_entry) -> option(sp_t27)
function sp_put_27(tree, key, base, value) = {
  var node : sp_t27 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 67108864 then {
    let old : option(sp_t26) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_26(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t26) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_26(old, key, base + 67108864, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_28 : (option(sp_t28), nat, nat) -> option(sp_entry)
function sp_get_28(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 134217728 then match node.zero { [||] => None(), child :: _ => sp_get_27(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_27(Some(child), key, base + 134217728) }
  }
}
val sp_put_28 : (option(sp_t28), nat, nat, sp_entry) -> option(sp_t28)
function sp_put_28(tree, key, base, value) = {
  var node : sp_t28 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 134217728 then {
    let old : option(sp_t27) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_27(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t27) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_27(old, key, base + 134217728, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_29 : (option(sp_t29), nat, nat) -> option(sp_entry)
function sp_get_29(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 268435456 then match node.zero { [||] => None(), child :: _ => sp_get_28(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_28(Some(child), key, base + 268435456) }
  }
}
val sp_put_29 : (option(sp_t29), nat, nat, sp_entry) -> option(sp_t29)
function sp_put_29(tree, key, base, value) = {
  var node : sp_t29 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 268435456 then {
    let old : option(sp_t28) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_28(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t28) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_28(old, key, base + 268435456, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_30 : (option(sp_t30), nat, nat) -> option(sp_entry)
function sp_get_30(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 536870912 then match node.zero { [||] => None(), child :: _ => sp_get_29(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_29(Some(child), key, base + 536870912) }
  }
}
val sp_put_30 : (option(sp_t30), nat, nat, sp_entry) -> option(sp_t30)
function sp_put_30(tree, key, base, value) = {
  var node : sp_t30 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 536870912 then {
    let old : option(sp_t29) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_29(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t29) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_29(old, key, base + 536870912, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_31 : (option(sp_t31), nat, nat) -> option(sp_entry)
function sp_get_31(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 1073741824 then match node.zero { [||] => None(), child :: _ => sp_get_30(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_30(Some(child), key, base + 1073741824) }
  }
}
val sp_put_31 : (option(sp_t31), nat, nat, sp_entry) -> option(sp_t31)
function sp_put_31(tree, key, base, value) = {
  var node : sp_t31 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 1073741824 then {
    let old : option(sp_t30) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_30(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t30) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_30(old, key, base + 1073741824, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get_32 : (option(sp_t32), nat, nat) -> option(sp_entry)
function sp_get_32(tree, key, base) = match tree {
  None() => None(),
  Some(node) => {
    if key < base + 2147483648 then match node.zero { [||] => None(), child :: _ => sp_get_31(Some(child), key, base) }
    else match node.one { [||] => None(), child :: _ => sp_get_31(Some(child), key, base + 2147483648) }
  }
}
val sp_put_32 : (option(sp_t32), nat, nat, sp_entry) -> option(sp_t32)
function sp_put_32(tree, key, base, value) = {
  var node : sp_t32 = match tree { None() => struct { zero = [||], one = [||] }, Some(x) => x };
  if key < base + 2147483648 then {
    let old : option(sp_t31) = match node.zero { [||] => None(), child :: _ => Some(child) };
    node.zero = match sp_put_31(old, key, base, value) { None() => [||], Some(child) => [|child|] }
  } else {
    let old : option(sp_t31) = match node.one { [||] => None(), child :: _ => Some(child) };
    node.one = match sp_put_31(old, key, base + 2147483648, value) { None() => [||], Some(child) => [|child|] }
  };
  Some(node)
}
val sp_get : (option(sp_t32), nat) -> option(sp_entry)
function sp_get(tree, key) = if key >= 4294967296 then None() else sp_get_32(tree, key, 0)
val sp_put : (option(sp_t32), nat, sp_entry) -> option(sp_t32)
function sp_put(tree, key, value) = if key >= 4294967296 then tree else sp_put_32(tree, key, 0, value)
val sp_concat : (list(nat), list(nat)) -> list(nat)
function sp_concat(xs, ys) = match xs {
  [||] => ys,
  x :: rest => x :: sp_concat(rest, ys)
}


struct sp_partition = { low : list(nat), high : list(nat) }

val sp_partition_at : (list(nat), int, list(nat), list(nat)) -> sp_partition
function sp_partition_at(xs, pivot, low, high) = match xs {
  [||] => struct { low = low, high = high },
  x :: rest => if x < pivot then sp_partition_at(rest, pivot, x :: low, high)
    else sp_partition_at(rest, pivot, low, x :: high)
}

val sp_radix_sort_fuel : (list(nat), int, int, nat) -> list(nat)
function sp_radix_sort_fuel(xs, base, span, depth) = {
  if depth == 0 then return xs;
  match xs { [||] => return xs, _ :: [||] => return xs, _ => () };
  if span <= 1 then return xs;
  let half = tdiv_int(span, 2);
  let cut = sp_partition_at(xs, base + half, [||], [||]);
  sp_concat(sp_radix_sort_fuel(cut.low, base, half, depth - 1),
    sp_radix_sort_fuel(cut.high, base + half, half, depth - 1))
}

termination_measure sp_radix_sort_fuel(xs, base, span, depth) = depth

val sp_radix_sort : (list(nat), int, int) -> list(nat)
function sp_radix_sort(xs, base, span) = sp_radix_sort_fuel(xs, base, span, 32)


