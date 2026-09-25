$property
function advance_is_field_multiplication(x : kword) -> bool = {
  advance(x) == kmul(x, 0x0000000000000002)
}

$property
function base_multiply_one(x : kword) -> bool = {
  kmul(x, 0x0000000000000001) == x
}

$property
function base_multiply_zero(x : kword) -> bool = {
  kmul(x, 0x0000000000000000) == 0x0000000000000000
}

$property
function embedding_has_zero_extension_limbs(x : kword) -> bool = {
  in_k(embed_k(x))
}
