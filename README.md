# leanISA in Sail

An Apache-2.0 research implementation of leanVM's six instruction families
in Sail, with Lean proofs and a reproducible C/Lean validation harness. The
Sail model is an independent reference; a full Rust-to-Sail correspondence
theorem remains open.

## Repository layout

| Path | Contents |
| --- | --- |
| [`spec/`](spec/machine.sail) | Sail ISA, encoding, arithmetic, BLAKE2S, and bounded O1/O2a/O2b runners |
| [`proofs/`](proofs/README.md) | Lean proofs and theorem scope |
| [`scripts/`](scripts/check.py) and [`tests/`](tests/test_harness.py) | Validation harness, differential cases, and regressions |
| [`dependencies/`](dependencies/algebra.lock.json) and [`upstreams.json`](upstreams.json) | Pinned build inputs |
| [`docs/`](docs/status.md) | Semantic contract, status, roadmap, and release evidence |

The Sail model covers **SET_CONSTANT, XOR, MUL_NATIVE, DEREF, JUMP, and
BLAKE2S**. Its immutable-image runner checks a supplied memory image. The
bounded operational runners add ordered advice (O1), equality propagation
(O2a), and caller-supplied MUL candidates (O2b). The Lean library proves
conditional instruction and runner results, indexed/scanning runner
equivalence, and arithmetic properties of the extracted Sail operations.
The exact premises and remaining Rust, solver, and compression obligations
are in [status](docs/status.md) and [correspondence](docs/correspondence.md).

## Validate

Prepare the pinned Sail, lean-sail, and leanVM checkouts, toolchain, and
offline algebra store as described in [validation](docs/validation.md).
From this repository root:

```sh
python3 -O scripts/check.py \
  --sail-root ../sail \
  --lean-support ../sail/_deps/lean-sail \
  --leanvm ../leanVM \
  --cases 64 --coverage
```

The default campaign compares generated C and Lean behavior, runs the
O1/O2a/O2b controls, checks SMT properties, builds the Lean proofs, and
audits their axioms. The [release record](docs/release.md) links the report
for this source snapshot. Generated build output is ignored.

For shared arithmetic, encoding, BLAKE2S, and final-image testing against
both Rust leanVM and Lean leanerVM, use the
[three-target differential campaign](docs/differential.md). It supports
seeded generation, directed boundary cases, deterministic replay, and saved
failures.

Original work is licensed under [Apache-2.0](LICENSE). See
[third-party notices](THIRD_PARTY_NOTICES.md) for external inputs.
