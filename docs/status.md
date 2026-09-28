# Research snapshot status

This page separates established Sail and Lean results from the remaining
whole-ISA correspondence work. The [release record](release.md) gives the
validation result for this source tree, and the [roadmap](roadmap.md) lists
the next proof gates.

## Accepted scope

| Area | Result and boundary |
| --- | --- |
| Sail ISA | [Six typed instructions](../spec/machine.sail), canonical eight-word encoding, immutable-image `run`, and indexed `run_indexed`. The [contract](semantics.md) states sentinel, input, address, and raw-bytecode boundaries. |
| O1 | [Bounded forward execution](../spec/forward.sail) with partial memory, stable eager observations, deferred Cell equalities, ordered advice, and a completed-image checker. The validation campaign includes 49 complete envelopes and five targeted mutants. |
| O2a | [Equality-only sparse execution](../spec/o2a_sparse_runner.sail) propagates fixed values across deferred equality components, rejects conflicts, and defaults unresolved components. The campaign includes 26 complete C/Lean/slow-control envelopes and negative controls. |
| O2b | [Bounded explicit MUL advice](../spec/o2b_candidate.sail) scans at most 64 supplied plans and retains at most eight matching candidates; the first compatible product is checked under Sail `emul`. Checked tags require immutable-image checker state and verdict agreement. The campaign includes 47 directed C/Lean envelopes, 26 O2a parity envelopes, source mutants, and corruption controls. |
| Lean execution | [Conditional instruction and runner proofs](../proofs/WholeISA.lean) cover all six instructions, compatible observations and completion, finite prefixes, changing frames, repeated PCs, fuel, and sentinel outcomes. [Indexed runner equivalence](../proofs/IndexedRunner.lean) covers full Sail results, including error and fuel cases, under stated size premises. |
| Lean arithmetic | [Base multiplication](../proofs/PolynomialMultiplication.lean), [extension multiplication](../proofs/ExtensionMultiplication.lean), [base](../proofs/BaseField.lean) and [cubic](../proofs/ExtensionField.lean) field structure, and a [source-shaped Lean extension inverse](../proofs/F1e5c.lean) equal to its accepted reference. These concern extracted Sail operations and Lean models, not external Rust execution. |
| Differential testing | The [bounded three-target CLI](differential.md) invokes Sail, Rust leanVM and Lean leanerVM for full-limb arithmetic, encoding and BLAKE2S comparisons. Rust-produced final images are checked independently by both models. Seeded data generation, directed opcode/error/fuel cases, deterministic replay, saved failures and bounded primitive/image reduction are implemented. |

The [validation procedure](validation.md) runs the complete C/Lean, SMT,
proof, axiom, and operational-runner checks. Its machine-readable result is
linked from the [release record](release.md).

## Open obligations

- Prove source-bound O1/O2a/O2b generated-runner results satisfy the Lean
  instruction and whole-runner policies, including checker agreement and
  completed-image invariants.
- Establish automatic inverse-derived MUL advice and broader solver
  correctness. O2b currently accepts caller-supplied bounded candidates.
- Establish an admissible Rust execution trace boundary, then prove its
  arithmetic, layout, encoding, addressing, control-flow, and checker
  correspondence to Sail. Current Rust execution does not by itself satisfy
  every stable-observation premise.
- Prove BLAKE2S compression against an independent mathematical reference
  and relate the actual Rust/hash implementation separately.
- Extend the [bounded differential CLI](differential.md) with structural
  control-flow/advice fuzzing, a general program/advice/image interface and
  reduction of Rust program-generation failures. No proof-system soundness
  or compiler correctness claim follows from the current ISA work.

See [correspondence](correspondence.md) for the semantic split and
[roadmap](roadmap.md) for the next gates.
