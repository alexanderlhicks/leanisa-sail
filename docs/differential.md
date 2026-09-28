# Three-target differential testing

[`scripts/differential.py`](../scripts/differential.py) invokes the actual Sail
specification, Rust leanVM, and Lean leanerVM implementation. The adapters
perform input/output conversion and call their targets; none contains a second
VM evaluator. This campaign is separate from the existing Sail C/Lean proof and
validation campaign.

## Prepare and run

Use the exact revisions in [`targets.json`](../tests/differential/targets.json).
Prepare the Sail compiler, C compiler, GMP, offline Cargo dependencies,
and Rust checkout as described in
[validation](validation.md). Install leanerVM's pinned Lean 4.33.1 toolchain,
its pinned CompPoly checkout under `.lake/packages/CompPoly`, and Mathlib's
prepared dependency caches. One minimal setup, run from the parent directory
of this repository, is:

```sh
git clone https://github.com/Verified-zkEVM/leanerVM leanerVM
git -C leanerVM checkout --detach 97ac443ae91d106333c1482b7164dc12c174bbe1
mkdir -p leanerVM/.lake/packages
git clone https://github.com/Verified-zkEVM/CompPoly leanerVM/.lake/packages/CompPoly
git -C leanerVM/.lake/packages/CompPoly checkout --detach 3468b38c8fd270f93f55a259220a8abc544e7437
elan toolchain install leanprover/lean4:v4.33.1
(cd leanerVM/.lake/packages/CompPoly && lake exe cache get)
cd leanisa-sail
export LEANERVM_DEPENDENCIES_DIR=../leanerVM/.lake/packages/CompPoly/.lake/packages
```

This resolves the checked-in CompPoly manifest and obtains Mathlib's cache;
the differential helper itself does not fetch dependencies. The commands
return to this repository and select that prepared cache directory. Keep the
pinned sources and manifests clean. The helper verifies source revisions
and records hashes of available prepared dependency-cache artifacts. Those
caches are trusted build inputs, rather than source-rebuilt Mathlib evidence.
It rebuilds the CompPoly and leanerVM import cone from source in the campaign
directory, and the runner checks staged interpreter artifacts and cache hashes
before and after the campaign.

```sh
python3 -O scripts/differential.py \
  --sail-root ../sail \
  --leanvm ../leanVM \
  --leanervm ../leanerVM \
  --seed 20260928 --cases 16
```

If Mathlib's packages are prepared separately, set
`LEANERVM_DEPENDENCIES_DIR` to that Lake packages directory. This directory is
read only. The upstream checkouts are also read only; build products and
diagnostics go under the ignored `build/differential/` directory. A fresh
adapter build has a separate `--build-timeout` (default 1,200 seconds).

The Lean adapter uses the pinned interpreter (`lean -j1 --run`). This avoids
eager native initialization of the pinned base field's `Fintype` enumeration.
No dependency source is patched. The required modules are elaborated before
execution, and warnings are errors. See the
[Rust adapter notes](../tests/differential/README.rust.md) for its API and
execution scope.

## What is compared

| Cases | Compared results |
| --- | --- |
| Base and cubic extension field addition and multiplication | Base result and all three extension limbs |
| Encoding of all six instruction families and three DEREF modes | All eight bytecode columns; Sail also checks decoding round trips |
| BLAKE2S compression | All 256 output bits, arbitrary input/CV words, counter and raw flag words |
| Hand-assembled Rust execution | Actual exported final memory checked independently by Sail and leanerVM, plus instruction encoding |

Rust execution constructs a witness. Sail's `run_indexed` and leanerVM's
`checkWithinFuel` check the same immutable final image. leanerVM does not expose
an operational witness generator. The program part therefore compares Rust
witness production against two independent checkers. It does not claim three
identical forward executors. `run_indexed` is the specification's indexed
immutable-image runner; its equivalence with scanning `run` is proved in the
existing library.

The Rust adapter uses empty hints and filler lists. Its actual `base_counts`
must sum to the exported main cycles. On successful checks, leanerVM's actual
halt step count, PC, and FP must match that execution count and Sail's final
state. All six opcode execution counters must be nonzero in a standard
campaign; static instruction presence alone does not satisfy the gate.

The seeded generator randomizes complete field values, BLAKE inputs and raw
metadata, and initialized 32-instruction program data. Program structure uses
a bounded template with SET, XOR, MUL, all DEREF modes, BLAKE, taken and untaken
JUMP. The directed corpus adds operand aliases, a changed/restored frame,
singleton sentinel behavior, deferred equality, back-solving, and known
read-before-write counterexamples. It retains the accepted expected outcomes
of those counterexamples. Arbitrary control-flow and hint-generating program
fuzzing remain outside this initial profile.

Every successful Rust image is checked with zero, exact, insufficient, and
surplus fuel, and with a corrupted public input cell. Surplus fuel is omitted
when exact fuel is already the profile maximum of 1,024. Initialized templates
also corrupt the SET, XOR, MUL, DEREF and BLAKE cells individually. Fuel is
counted in main execution steps, with the sentinel checked before exhaustion.

## Shared domain and outcomes

The [request schema](../tests/differential/request.schema.json) describes the
JSON-lines requests. The Python validator also enforces distinct sparse-cell
indices and indices below the requested memory size.

- Word limbs are exactly 16 lowercase hexadecimal digits, least significant
  first. No extension limb is truncated.
- Offsets are generator exponents and are converted by each actual target.
  The campaign caps offsets at 65,535 because Rust's `bytecode_columns` builds
  a table through the largest offset. This resource bound is narrower than
  the ISA's `u32` offsets.
- Programs contain at most 64 instructions and have power-of-two lengths,
  including encoding requests. Shared final images contain 65,536 or 131,072 cells;
  unspecified cells are zero. Fuel is at most 1,024.
- BLAKE metadata consists of a 64-bit counter and two raw 32-bit flags. Its
  third word limb is zero. Flags are not converted to Boolean values.
- leanerVM exposes `fuelExhausted` separately. It combines some access/value
  failures as `invalidStep`, and exposes public-boundary and frame errors.
  The adapter retains the raw error. `Rejected` may match Sail's `BadAccess`,
  `BadValue`, or `BadInstance`; it may not match `Halted` or `OutOfFuel`.
  Failure-register equality is outside that coarse error API.

Adapter input rejection, panic, crash, timeout, missing response, and malformed
output all fail the campaign. They are separate from semantic checker
rejections. Runtime processes have an 8 GiB address-space limit, an elapsed
deadline (default 120 seconds per invocation/batch), and a monitored 16 MiB
output bound; exceeding a bound terminates the process group. The initial
runner requires Linux/POSIX process and resource APIs.

The Rust revision named by leanerVM differs from this repository's existing
Rust pin. The [source comparison](../tests/differential/rust-source-drift.json)
records the identical arithmetic, representation, encoding and BLAKE source
pieces and the execution changes. The comparison covers hand-assembled
programs with no hints, fillers, proving, or compiled-program pipeline.

## Replay, reduction, and evidence

Each campaign writes its exact input corpus to `build/differential/corpus.json`
and replays each target deterministically. A successful `report.json` contains
the pins, source hashes, adapter/build hashes, precise compared outputs,
execution counters, and case coverage. It is written after all gates pass.
The [accepted validation receipt](differential-report.json) summarizes the
independently validated default corpus and its exact replay.
An old report is removed before setup; a failure after option parsing cannot
leave a stale success report.

Command-line syntax errors reported by `argparse` do not start a campaign.
Once options have parsed, numerical range errors also clear the previous
report and produce a failure record.

```sh
python3 -O scripts/differential.py \
  --sail-root ../sail --leanvm ../leanVM --leanervm ../leanerVM \
  --replay build/differential/corpus.json
```

Failures are saved to `failure.json` with the offending input, target outcomes,
and provenance. Pass `--minimize 32` to try up to 32 reductions of a primitive,
encoding, or fixed-image failure. Reductions preserve the failing targets,
their success/failure classes, and their inequality relation; image reductions
also preserve the exact semantic verdict classes. A mismatch cannot reduce to
a crash, malformed input, timeout, or a different checker error class. Rust
program generation failures are saved intact. Replay a failure with
`--replay build/differential/failure.json`; responses are recomputed by the
actual targets. Explicit fixed-image replay compares the two checkers and
does not assert that Rust generated that reduced image.

The acceptance controls reject omitted targets, agreeing wrong outputs,
truncated codec/digest/field results, changed halt counts/registers, altered
error classes, malformed replies and process failures:

```sh
python3 -O -m unittest discover -s tests -p test_differential.py
```

Passing bounded tests gives evidence for the inputs run. It does not establish
universal ISA correspondence, compiler correctness, prover/verifier agreement,
or cryptographic soundness. The remaining proof boundaries are in
[correspondence](correspondence.md).
