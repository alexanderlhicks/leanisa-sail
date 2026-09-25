#!/usr/bin/env python3
"""Create isolated semantic mutants of the accepted O2a sparse runner."""

from __future__ import annotations

import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "spec/o2a_sparse_runner.sail"
MUTATIONS = {
    "pair_activation": (
        ("w = o2s_activate(w, small.members, None(), large.value, false)",
         "w = w"),
        ("w = o2s_activate(w, large.members, None(), small.value, false)",
         "w = w"),
    ),
    "output_activation": (
        ("if fresh then o2s_fix_root(w, index, value, Some(index), false) else w",
         "if fresh & origin != O2aOutput then "
         "o2s_fix_root(w, index, value, Some(index), false) else w"),
    ),
    "eager_activation": (
        ("if fresh then o2s_fix_root(w, index, sail_zeros(192), "
         "Some(index), false)\n  else w", "w"),
    ),
    "activation_order": (
        ("let sorted = sp_radix_sort(members, 0, 4294967296);",
         "let sorted = members;"),
    ),
}


def generate(out: Path) -> None:
    source = SOURCE.read_text()
    out.mkdir(parents=True, exist_ok=True)
    for name, replacements in MUTATIONS.items():
        mutant = source
        for old, new in replacements:
            if mutant.count(old) != 1:
                raise RuntimeError(f"{name}: source anchor missing or duplicated: {old!r}")
            mutant = mutant.replace(old, new, 1)
        if mutant == source:
            raise RuntimeError(f"{name}: mutation is ineffective")
        (out / f"{name}.sail").write_text(mutant)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    generate(args.out)


if __name__ == "__main__":
    main()
