# Validate this source snapshot

The default campaign compiles the Sail specification to C and Lean, compares
the same generated corpus in both backends, runs Rust differential and Python
reference checks, checks SMT properties, builds the handwritten Lean proof
library, and audits the axioms of every owned declaration. O1, O2a, and O2b
also have directed two-backend, mutation, and negative-control gates. A
single-backend invocation is diagnostic and does not execute those complete
operational gates.

## Pinned prerequisites

Install Python 3, a C compiler and GMP development headers, Rust/Cargo, Elan,
and the tools in [upstreams.json](../upstreams.json). Prepare sibling or
explicit checkouts of Sail, its lean-sail support library, and leanVM at the
pinned revisions; build Sail with its C, Lean, and SMT backends and the pinned
Z3. Rust runs use the checked-in Cargo lockfiles and `--offline --locked`, so
populate the Cargo cache first. The proof build uses Lean 4.29.0 and the
packages in [algebra.lock.json](../dependencies/algebra.lock.json).

Prepare the Lean algebra store from pinned local sources and the pinned
ProofWidgets JS archive as described by the command help:

```sh
python3 scripts/algebra_dependencies.py setup --help
python3 scripts/algebra_dependencies.py setup \
  --sources /path/to/pinned/mathlib \
  --js-archive /path/to/ProofWidgets4-v0.0.95.tar.gz
```

The setup command verifies revisions, source and artifact hashes, and offline
replay. It does not download dependencies. The `build/` directory is ignored
and contains generated outputs and the prepared algebra store.

## Full local gate

From the repository root, run sequentially with one owner of the generated
build and algebra store:

```sh
python3 -O scripts/check.py \
  --sail-root /path/to/sail \
  --leanvm /path/to/leanVM \
  --cases 64 --coverage
python3 -m unittest discover -v -s tests -p test_harness.py
python3 -O -m unittest discover -v -s tests -p test_harness.py
python3 -m unittest discover -v -s tests -p test_algebra_dependencies.py
python3 -O -m unittest discover -v -s tests -p test_algebra_dependencies.py
```

`scripts/check.py` also accepts `--lean-support` and `--algebra-store` for
prepared paths outside this checkout. The harness proof regressions use the
default store at `build/dependencies/lean-algebra`; prepare that store before
running the bare `unittest` commands above, even if the full campaign used an
external `--algebra-store`. Do not run concurrent Lake writers against one
output or algebra store. The campaign writes `build/validation.json`
only after its required gates pass. A failed or interrupted run is not
acceptance evidence.

The [release record](release.md) states the historical O2b acceptance and
the validation status of this curated snapshot. A fresh run of the commands
above checks these exact public sources; it does not prove the open
[correspondence obligations](correspondence.md).
