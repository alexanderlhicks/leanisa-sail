# Whole-ISA research roadmap

The target is an executable Sail ISA and a justified connection from
admissible leanVM executions to its immutable-image checker. The current
[status](status.md) identifies accepted executable and Lean results;
[correspondence](correspondence.md) states the boundary that remains.

| Gate | Next acceptance result |
| --- | --- |
| O1/O2a/O2b policy bridge | Relate actual generated operational runners to accepted [six-instruction](../proofs/WholeISA.lean) and bounded-runner policies. Derive completed-image and checker state/verdict agreement; preserve sentinel, fuel, failure priority, aliases, and pending Cell equalities. |
| Solver completion | Extend [O2b explicit advice](../spec/o2b_candidate.sail) to justified inverse-derived plans. Prove candidate selection, compatibility, conflict/resource diagnostics, provenance, and final checker behavior for the generated runner. |
| R1 Rust admissibility | Specify and validate which Rust traces preserve eager observations, address representations, advice and deferred equalities, and separate architectural memory from witness-table filling. Keep known disagreements as regressions. |
| R2 Rust correspondence | Prove the admitted executor's field arithmetic, inverse, layout, bytecode/offset conversion, state transitions, and terminal results refine the [Sail contract](semantics.md), with explicit external and compiler assumptions. |
| H1 compression | Prove the [Sail BLAKE2S implementation](../spec/blake2s.sail) against an independent compression definition, including chunks, rounds, counters, and arbitrary flag patterns; relate Rust compression separately. |
| Tooling and release | Extend the delivered [bounded three-target CLI](differential.md), seeded data generation and replay with structural control-flow/advice fuzzing, a general program/advice/image interface and Rust program-failure reduction. Revalidate each source snapshot against an exact manifest; accepted results are in the [release record](release.md). |

For every gate, record exact source pins, explicit premises, kernel or
executable checks as appropriate, negative controls, and an independent
adversarial review. A passing bounded C/Lean campaign is evidence for tested
cases; it does not discharge a universal theorem. A theorem about extracted
Sail does not establish Rust or cryptographic proof-system correctness. See
[validation](validation.md) for replay procedure and trust limits.
