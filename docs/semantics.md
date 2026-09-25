# Semantic contract

This model targets leanVM revision `48a904208d682848dac0e18ef8b01ebfc40df9ad`. The primary architectural description is [VM specification, section 2](https://github.com/leanEthereum/leanVM/blob/48a904208d682848dac0e18ef8b01ebfc40df9ad/doc/leanvm/body/02-vm-specification.tex). The [executor](https://github.com/leanEthereum/leanVM/blob/48a904208d682848dac0e18ef8b01ebfc40df9ad/crates/lean_vm/src/cpu/execute.rs), [bytecode layout](https://github.com/leanEthereum/leanVM/blob/48a904208d682848dac0e18ef8b01ebfc40df9ad/crates/lean_vm/src/cpu/layout.rs), and [instruction tables](https://github.com/leanEthereum/leanVM/blob/48a904208d682848dac0e18ef8b01ebfc40df9ad/crates/lean_vm/src/tables.rs) provide separately checked implementation references. A disagreement between them is not silently resolved by making Rust the definition of correctness.

## Representation

`kword` is a 64-bit polynomial encoding: bit i is the coefficient of x^i, with reduction polynomial x^64 + x^4 + x^3 + x + 1. `kmul` uses fixed-length shift-and-reduce multiplication. `eword` is 192 bits, with its low, middle, and high 64-bit limbs representing coefficients on 1, y, and y², and y³ = y + 1. Addition is bitwise XOR. `emul` uses nine base products and explicit polynomial reduction. The reference implementation deliberately differs from the optimized Rust kernels.

The address generator is the encoding `0x0000000000000002`. This is the polynomial x, not the natural-number cast of two into a characteristic-two field. Address i is g^i. The memory vector's numeric index i names that address; pointer addition in ordinary integers is not an ISA operation. Relative operands are field elements multiplied by the current frame pointer.

## State and memory

The architectural state is `(pc, fp)`, both `kword`s. A fixed memory vector assigns one complete word to every address in its domain. Its addresses are g^0 through g^(length-1). Zero and values outside that finite sequence fail; failure is never silently converted into a zero-valued memory word. `read_memory` and `fetch` retain the direct scanning definitions.

`run_indexed` has the same inputs and intended results as `run`, but builds one immutable address index covering the larger of the memory and program domains, then uses `step_indexed` and `fetch_indexed`. This table contains two slots per address, hashes the field encoding, and resolves collisions by bounded linear probing with full-key comparisons. Resolved offsets are checked against the particular memory or program vector, so a larger shared index does not enlarge either address domain. Index construction and lookup are defined in Sail and extracted to both C and Lean. Construction uses linear space and expected linear time; queries take expected constant time, with a bounded full-table scan in the worst case. `run` retains scanning execution, which can be preferable for short or low-address workloads because it avoids index setup.

The index is an execution aid, not architectural state or witness data. Callers using `read_memory_indexed`, `step_indexed`, or `fetch_indexed` directly must supply an unmodified index from `build_address_index` covering their vector's domain. The public vector representation does not enforce that invariant against a forged or incomplete index. `step` selects the scanning memory path using an empty index; `run_indexed` constructs its own index. Singleton halts and zero-fuel runs return before allocating it. Repeated calls to `run_indexed` rebuild the index; callers checking many steps against the same domains can build it once and reuse `step_indexed`.

`step(state, instruction, memory)` checks the instruction's relation on this same memory image and returns either the next register state or an error. On error, the returned register state is unchanged. No instruction changes the image. This is the read-only interpretation of write-once memory used when checking a proof witness. The same cell cannot take different values on different steps. Arbitrary initial image values are allowed, except where public input and instructions constrain them.

This interface makes reads before operational writes meaningful: the prover may have supplied those values in advance. It does not implement allocator state, hint streams, back-solving a missing MUL operand, deferred DEREF filling, or Rust's default zero for an unwritten cell. Those are witness-generation policies, whose correspondence to the image relation needs its own specification and proof.

[Execution-to-image correspondence](correspondence.md) states a sufficient policy: eager observations fix their values, later assignments preserve them, and deferred equalities are checked on the completed image. Its observation-preservation theorem is proved in Lean. The current Rust executor does not enforce this policy, and its final `unconstrained_reads` list cannot certify image validity. The regression corpus covers arithmetic, control-flow, and aliasing disagreements, as well as valid unwritten values, deferred DEREF resolution, and MUL back-solving.

## Instruction relations

All instructions except JUMP advance pc by multiplying by g and preserve fp.

| Instruction | Required relation |
| --- | --- |
| XOR | The destination equals the XOR of the two full 192-bit source words. |
| MUL_NATIVE | The destination equals their product in the specified cubic extension. |
| SET_CONSTANT | The destination equals the supplied 192-bit immediate. |
| DEREF | The pointer source is in K; the derived target address is valid; the target equals the selected source. Cell mode uses a local word, Pc mode uses g²·pc embedded into E, and Fp mode uses fp embedded into E. The local o3 address must be valid in all three modes. |
| JUMP | All three local words are in K, including target and frame pointer on fallthrough. A nonzero condition selects those register values; zero advances pc and preserves fp. |
| BLAKE2S | Seven input and two output cells are canonical 128-bit embeddings. Four message references are independent; chaining value and output each occupy two consecutive cells. The output equals scalar BLAKE2s compression. |

BLAKE metadata is a 64-bit byte counter followed by two 32-bit flag words, all little-endian. The model accepts every bit pattern of those flags, matching the compression primitive's interface. Restricting them to Boolean or all-ones flags would change the ISA domain. The scalar mixing function follows [RFC 7693 sections 2 and 3](https://www.rfc-editor.org/rfc/rfc7693.html#section-3); the second flag word and arbitrary flag patterns are the broader leanVM compression interface. Hash-mode vectors additionally check interoperability with Python's BLAKE2s implementation.

## Execution boundary

`run(program, image, public_input, fuel)` starts with pc = fp = 1. It checks power-of-two sizes, 1 ≤ program length ≤ 2^32, and 2^16 ≤ memory length ≤ 2^32. Public input is 256 bits: its low and high 128-bit halves must equal memory cells 0 and 1 respectively, each with a zero top limb.

The last program address is a sentinel. `run` checks it before fetching. Reaching it succeeds only with fp = 1. This follows the pinned Rust executor and state boundary. It deliberately resolves the document's post-execution halt test in favor of the implementation; the singleton-program regression exposes the difference. The instruction stored at the sentinel is never executed, even if it is malformed semantically. A raw decoder is a separate interface.

Fuel bounds host execution, not the ISA's possible trace length. `OutOfFuel` means that no verdict was reached within the budget. It is neither successful execution nor a proof of divergence. A program that reaches the sentinel on its final permitted step succeeds.

The supplied image represents architectural memory, not the SNARK's full collection of witness tables. Table padding, read-count multiplicities, per-table instance caps, and Flock/PCS layouts are outside this function.

## Encoding and domain boundaries

Each encoded instruction is eight K words: opcode and seven operand slots. The opcodes are g^0 through g^5, respectively XOR, MUL, SET, DEREF, JUMP, BLAKE. SET's three immediate limbs occupy slots 2, 3, 4. DEREF's Pc and Fp flags occupy slots 4 and 5. BLAKE uses every operand slot. Unused slots are zero.

The decoder accepts exactly encodings produced by this field-operand instruction type: it checks the opcode, DEREF flags, and all unused slots by re-encoding. It does not decide whether every operand is a small nonnegative g-power representable by Rust's u32 offsets. Actual memory accesses are checked during execution.

The raw verifier can have a broader field-array domain than this canonical decoder. No correspondence theorem for arbitrary raw verifier bytecode is claimed. In particular, canonical decoding is an explicit interface restriction, not a repair made to upstream verification. Likewise, the executor's pre-fetch halt convention does not prove that the AIR prohibits extra execution at a JUMP sentinel.

Rust's u32 offset arithmetic and its bounded pointer-resolution table impose additional implementation considerations. Sail uses the document's field multiplication for effective addresses. Differential program tests exercise bounded offsets without integer overflow or address wraparound; they do not settle agreement outside that domain. Future proofs must state this domain or reconcile the behavior explicitly.
