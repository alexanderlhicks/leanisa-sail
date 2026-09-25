#!/usr/bin/env python3
"""Create five isolated O1 semantic mutants for directed validation."""

from __future__ import annotations

import argparse
import shutil
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "spec/forward.sail"
MUTATIONS = {
    "eager_default": (
        "w.cells[index] = Some(sail_zeros(192));",
        "w.cells[index] = None();",
    ),
    "deferred_pair": (
        "w.pending = pair :: w.pending;",
        "w.pending = w.pending;",
    ),
    "shape_priority": (
        "| length(initial) < 65536 | length(initial) > 4294967296",
        "| length(initial) < 2 | length(initial) > 4294967296",
    ),
    "fuel_order": (
        """if w.registers.pc == sentinel then {
      let verdict = if w.registers.fp == 0x0000000000000001 then Halted
        else BadValue;
      return o1_complete(w, program, public_input, fuel, verdict)
    };
    if i == fuel then
      return o1_complete(w, program, public_input, fuel, OutOfFuel);""",
        """if i == fuel then
      return o1_complete(w, program, public_input, fuel, OutOfFuel);
    if w.registers.pc == sentinel then {
      let verdict = if w.registers.fp == 0x0000000000000001 then Halted
        else BadValue;
      return o1_complete(w, program, public_input, fuel, verdict)
    };""",
    ),
    "failure_priority": (
        """let pointer = o1_value(w, ip);
      let rt = o1_resolve(w, index, kmul(pointer[63..0], o2)); w = rt.work;
      if w.status != O1Running then return w;
      if not_bool(in_k(pointer)) then
        return o1_fail(w, O1OperandOutsideK, O1PolicyPhase, ip, 0);""",
        """let pointer = o1_value(w, ip);
      if not_bool(in_k(pointer)) then
        return o1_fail(w, O1OperandOutsideK, O1PolicyPhase, ip, 0);
      let rt = o1_resolve(w, index, kmul(pointer[63..0], o2)); w = rt.work;
      if w.status != O1Running then return w;""",
    ),
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    source = SOURCE.read_text()
    args.out.mkdir(parents=True, exist_ok=True)
    for name, (before, after) in MUTATIONS.items():
        require(source.count(before) == 1, f"mutation anchor not unique: {name}")
        variant = args.out / name
        variant.mkdir(exist_ok=True)
        (variant / "spec").mkdir(exist_ok=True)
        (variant / "tests").mkdir(exist_ok=True)
        for source_name in ("field.sail", "blake2s.sail", "machine.sail"):
            shutil.copy2(ROOT / "spec" / source_name,
                         variant / "spec" / source_name)
        for test_name in ("o1_print.sail", "o1_cases.sail", "o1_compare.py"):
            shutil.copy2(ROOT / "tests" / test_name,
                         variant / "tests" / test_name)
        (variant / "spec/forward.sail").write_text(source.replace(before, after, 1))
        print(variant)


if __name__ == "__main__":
    main()
