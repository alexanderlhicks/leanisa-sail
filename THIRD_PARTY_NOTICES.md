# Third-party provenance

The root [Apache-2.0 license](LICENSE) covers the original material in this
repository. It does not change the terms of upstream projects or material
copied from them. This file records provenance and license information for
the pinned dependencies and the sources retained in this public snapshot.

## External build and comparison inputs

The following source checkouts and build assets are **not vendored** here.
Their revisions or receipts are recorded in [upstreams.json](upstreams.json),
[dependencies/algebra.lock.json](dependencies/algebra.lock.json), and the
[three-target pins](tests/differential/targets.json).

| Input | Role | Upstream license information |
| --- | --- | --- |
| [Sail](https://github.com/rems-project/sail) | Compiler and backends; produces C and Lean evidence | BSD-2-Clause with exceptions described in the pinned [license](third_party/licenses/sail/LICENSE) and [third-party file list](third_party/licenses/sail/THIRD_PARTY_FILES.md). |
| [lean-sail](https://github.com/rems-project/lean-sail) | Lean support library for extracted Sail code | The pinned checkout has no root license file; `Sail/BitVec.lean` refers to Apache-2.0. Resolve the missing root notice before distributing this support library or artifacts containing its source. |
| [leanVM](https://github.com/leanEthereum/leanVM) | Differential oracle and source correspondence target | The pinned checkout has `LICENSE-APACHE` and `LICENSE-MIT`; individual source notices may apply. |
| [leanerVM](https://github.com/Verified-zkEVM/leanerVM) | Independent Lean ISA implementation and immutable-image checker | Apache-2.0, as stated by the pinned root `LICENSE`. |
| [CompPoly](https://github.com/Verified-zkEVM/CompPoly) | leanerVM's binary-field implementation dependency | Apache-2.0, as stated by the pinned root `LICENSE`. |
| [Mathlib](https://github.com/leanprover-community/mathlib4) and its locked Lean packages | Proof dependencies | Consult each pinned package's license. The prepared closure includes Apache-2.0 packages and an MIT-licensed `Cli` package. |
| [ProofWidgets](https://github.com/leanprover-community/ProofWidgets4) JavaScript archive | Prepared Lean proof dependency | The archive is an external input; this repository records a hash receipt, not the archive. Consult its upstream license when redistributing the archive. |
| [Z3](https://github.com/Z3Prover/z3), Lean, Rust and GMP | Validation tools | Installed externally. Consult their respective distributions for license terms. |

## Source-shaped work and generated evidence

The base-field Itoh chain in [proofs/BaseItoh.lean](proofs/BaseItoh.lean)
follows the operation sequence of leanVM's pinned Rust
[`GF2_64` inverse](https://github.com/leanEthereum/leanVM/blob/48a904208d682848dac0e18ef8b01ebfc40df9ad/crates/primitives/src/field/gf2_64.rs).
Its design was also informed by a source-level CompPoly reuse assessment in
the separate research checkout; no CompPoly source is bundled here.
The Lean definitions and proofs are expressed for this repository's extracted
Sail operations. The Rust source and CompPoly package are external inputs;
their original source notices remain with those projects.

The full research checkout's frozen validation and proof evidence included
compiler-generated C/Lean files, `.olean` files, logs, and copied or variant
generated model code. This curated snapshot omits those captures and the
historical hash inventories; see the
[release scope](docs/release.md). Regenerating output with Sail or other
upstream tools does not grant a new license to their support code.

The two Sail notice files above are copied without modification from pinned
revision `ce60ba570b4402a42431bc5033145d9aeb327f20`. They document the
provenance of generated outputs that users may recreate. This repository
does not vendor the Sail compiler or its runtime headers.
