# Correspondence boundary

The [Sail model](../spec/machine.sail) is an independent executable
specification of leanISA's six instructions. The immutable-image `run` and
`run_indexed` check a supplied memory image. The [O1 runner](../spec/forward.sail)
constructs a partial image; [O2a](../spec/o2a_sparse_runner.sail) resolves
deferred Cell equalities; [O2b](../spec/o2b_candidate.sail) accepts bounded,
caller-supplied MUL plans. A checked generated result still depends on the
immutable-image checker agreeing with the completed image and verdict.

The [Lean proof sources](../proofs/README.md) establish properties of the
generated Sail definitions under their stated hypotheses. They include
conditional six-instruction and bounded runner simulation, canonical
encoding, indexed/scanning runner equality, finite-address support, and
field/inverse facts for Sail arithmetic. The theorem statements and imported
axioms, rather than this summary, define their exact scope. The proof build
and complete owned-declaration axiom audit are part of the
[validation campaign](validation.md).

Differential tests compare generated C and Lean outputs with a pinned Rust
adapter, independent Python arithmetic, and directed oracles. Those tests
provide bounded evidence for the cases run. They do not establish universal
equivalence to Rust execution or the correctness of the Sail compiler.

## Open bridges

- A source-semantics and admissibility refinement from actual Rust execution,
  arithmetic branches, layout, dispatch, and public API behavior to the Sail
  model remains open.
- Independent refinement of BLAKE2S compression to the external reference
  implementation remains open.
- The formal bridge from O1/O2a/O2b generated operations to the accepted
  whole-ISA policy runner remains open. Later private proof checkpoints are
  outside this curated source release.
- O2b accepts supplied bounded MUL plans. Automatic inverse-plan derivation,
  solver completeness, and caller-side decoding are not established.

The [semantic contract](semantics.md) gives instruction and execution
boundaries. The [status page](status.md) distinguishes the executable,
proved, tested, and still-open claims in this release.
