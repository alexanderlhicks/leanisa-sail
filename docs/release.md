# Release scope and validation

This Apache-2.0 research snapshot contains the Sail specification, Lean proof
sources, validation tools and tests, and pinned dependency records. Generated
build outputs, executables, run logs, and exploratory research are excluded;
structured validation and dependency receipts are retained. The
[source manifest](source-manifest.sha256) identifies the published files.

The accepted baseline covers bounded O1, O2a, and explicit-advice O2b runners.
The earlier private research archive is outside this repository; its frozen
campaign is not presented as public replay evidence. The result below comes
from a fresh campaign on the public sources. The [status](status.md) and
[correspondence](correspondence.md) pages state the proof boundaries.

The pinned algebra lock retains two historical local Lean/Lake path fields,
and its `reviewed_cache.evidence` field names an omitted private review file.
Validation checks pinned versions, binary hashes, receipts, and artifacts;
it does not load executables or review files from those paths. The compressed
receipt retains temporary build-path strings from dependency preparation.

## Curated source validation

On 2026-09-25 UTC, the full campaign on the curated tree exited zero
with both C and Lean backends, `--cases 64 --coverage`, the pinned external
Sail/lean-sail/leanVM checkouts, and a prepared external algebra store. The
unredacted `build/validation.json` has SHA-256
`46e357aaecfc81b101102ab491c5f96ccfa8c5252ac9648fd5e7d3b1dea13a63`.
The [public validation report](validation-report.json) preserves its results
and redacts only the local path in `lean_algebra.store`; its SHA-256 is
`21770e92b1eb36c2df3fb0a2300344964819448c25fa6086b12cf8449c097177`.
Independent review compared the two report structures and rehashed all 135
recorded source inputs without a mismatch.

The report records 171 baseline cases (128 field, 23 BLAKE2S, 20 execution),
four unsatisfiable SMT obligations, 79 Lean proof modules, and a passing audit
of 1,761 owned declarations with only `propext`, `Classical.choice`, and
`Quot.sound` as allowed axioms. O1 covers 49 two-backend cases and five source
mutants; O2a covers 26 complete envelopes, four source mutants, and four
output corruptions; O2b covers 47 directed cases, 20 source mutants, 14
output corruptions in each Python mode, and 26 O2a parity envelopes.

An independent validator rehashed the report's 135 top-level source inputs
and the 11 O1, 21 O2a, and 23 O2b child inputs; all matched. Four regression
suites passed with zero skips: harness normal 19/19, harness `-O` 19/19,
dependency normal 17/17, and dependency `-O` 17/17. They used the same
prepared external algebra store as the full campaign. The
[validation instructions](validation.md) give the default-store setup and
reproduction commands.

The [source manifest](source-manifest.sha256) hashes every file in this
public tree except itself; it excludes ignored build output and Git metadata.

## Three-target differential validation

On 2026-09-28 UTC, an independent validator ran the standard seeded
[three-target campaign](differential.md) and replayed its exact 201-input
corpus. Both runs passed: 80 field multiplications, 80 additions, 22 BLAKE2S
compressions, 18 encoding comparisons, 17 Rust executions, and 83 immutable
image checks. All 300 observations, execution counts, coverage, source
hashes, pins, and the corpus hash matched exactly. Actual execution covered
all six instruction families; all 12 accepted replay cases retain their
inputs and expected outcomes.

The [compact differential receipt](differential-report.json) records the
22 campaign source hashes, target and dependency pins, artifact digests,
coverage, and full/replay report hashes. Its SHA-256 is
`4dad826d581667ff3d10a4d84c3bb45ba62015569bcaf51558a31fc87fb342df`.
Acceptance controls passed 21/21 normally and 21/21 under `-O`, followed by
17 independent adversarial checks and two actual saved-count
failure/reduction/replay rounds. Run logs and full local reports are omitted.

Primitive results are compared across all three targets. Rust produces
program witnesses, which Sail and leanerVM check independently. leanerVM
uses its pinned Lean 4.33.1 interpreter, with rebuilt CompPoly and leanerVM
modules and explicitly trusted prepared dependency caches. Arbitrary
control-flow and hint-generating fuzzing remain outside this bounded profile.

## Public trust boundary

The theorem statements and source files define the proof claims. The
validation campaign checks the generated C/Lean behavior on its corpus,
builds the handwritten Lean library, and audits its axioms. It does not
establish Sail compiler correctness or universal Rust-to-Sail refinement.
See [status](status.md), [correspondence](correspondence.md), and
[third-party provenance](../THIRD_PARTY_NOTICES.md).
