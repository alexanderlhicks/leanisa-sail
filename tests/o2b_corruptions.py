#!/usr/bin/env python3
"""Mutate both backend envelopes identically and demand literal rejection."""

from __future__ import annotations

import argparse
from pathlib import Path

from o2b_compare import require, verify


def replace_once(lines: list[str], old: list[str], new: list[str]) -> None:
    positions = [i for i in range(len(lines) - len(old) + 1)
                 if lines[i:i + len(old)] == old]
    require(len(positions) == 1, f"corruption anchor count: {old!r}")
    i = positions[0]
    lines[i:i + len(old)] = new


def alter(data: bytes, name: str, change) -> bytes:
    lines = data.decode("utf-8").splitlines()
    positions = [i for i, line in enumerate(lines) if line == name]
    require(len(positions) == 1, f"corruption case anchor: {name}")
    start = positions[0]
    end = lines.index("END_O2b_ENVELOPE", start) + 1
    segment = lines[start:end]
    change(segment)
    lines[start:end] = segment
    return ("\n".join(lines) + "\n").encode()


def swap_first_two_cases(data: bytes) -> bytes:
    lines = data.decode("utf-8").splitlines()
    require(lines[0] == "EMPTY_PARITY", "first case order anchor")
    first_end = lines.index("END_O2b_ENVELOPE") + 1
    require(lines[first_end] == "UNEXECUTED_PARITY", "second case order anchor")
    second_end = lines.index("END_O2b_ENVELOPE", first_end) + 1
    return ("\n".join(lines[first_end:second_end] + lines[:first_end] +
                      lines[second_end:]) + "\n").encode()


def set_solver(lines: list[str]) -> None:
    require(lines[1:3] == ["BEGIN_O2b_ENVELOPE", "4"],
            "total-limit solver anchor")
    lines[2] = "3"


def set_ordinal(lines: list[str]) -> None:
    replace_once(lines,
        ["CHOICE", "1", "1", "SOME", "2", "SOME", "3"],
        ["CHOICE", "1", "0", "SOME", "2", "SOME", "3"])


def lose_some_zero(lines: list[str]) -> None:
    replace_once(lines,
        ["CHOICE", "0", "0", "SOME", "0", "SOME", "3"],
        ["CHOICE", "0", "0", "NONE", "SOME", "3"])


def set_origin(lines: list[str]) -> None:
    replace_once(lines, ["RUN", "3", "1", "FIXED", "2", "9", "2"],
                 ["RUN", "3", "1", "FIXED", "2", "4", "2"])


def advice_event_as_prerun(lines: list[str]) -> None:
    start = lines.index("END_PAIRS") + 1
    end = lines.index("END_EVENTS")
    events = lines[start:end]
    require(len(events) % 14 == 0 and events[6 * 14] == "13",
            "MUL advice event anchor")
    events[6 * 14] = "1"
    lines[start:end] = events


def swap_advice(lines: list[str]) -> None:
    start = lines.index("END_PAIRS") + 1
    end = lines.index("END_EVENTS")
    events = lines[start:end]
    require(len(events) % 14 == 0 and len(events) // 14 == 12,
            "fresh event count for swap")
    first, second = events[6 * 14:7 * 14], events[7 * 14:8 * 14]
    require(first[0] == second[0] == "13", "advice event anchor")
    events[6 * 14:8 * 14] = second + first
    lines[start:end] = events


def reverse_pair(lines: list[str]) -> None:
    replace_once(lines, ["END_CELLS", "3", "4", "END_PAIRS"],
                 ["END_CELLS", "4", "3", "END_PAIRS"])


def cap_with_candidate_event(lines: list[str]) -> None:
    end = lines.index("END_EVENTS")
    event = ["13", "2", "8", "0", "1", "1", "0", "3", "0", "2",
             "0", "9", "1", "0"]
    lines[end:end] = event


def coordinated_checker_pc(lines: list[str]) -> None:
    index = lines.index("BEGIN_O2a_ENVELOPE")
    require(lines[index + 8] == "2" and lines[index + 10:index + 12]
            == ["CHECKER", "2"], "checker PC anchor")
    lines[index + 8] = "3"
    lines[index + 11] = "3"


def wrong_product(lines: list[str]) -> None:
    replace_once(lines, ["RUN", "5", "1", "FIXED", "6", "6", "6"],
                 ["RUN", "5", "1", "FIXED", "7", "6", "7"])


def wrong_phase(lines: list[str]) -> None:
    index = lines.index("BEGIN_O2a_ENVELOPE")
    require(lines[index + 2] == "8", "diagnostic phase anchor")
    lines[index + 2] = "7"


def diagnostic_as_checked(lines: list[str]) -> None:
    index = lines.index("BEGIN_O2a_ENVELOPE")
    require(lines[index + 3] == "0", "diagnostic tag anchor")
    lines[index + 3] = "3"


def wrong_event_problem(lines: list[str]) -> None:
    end = lines.index("END_EVENTS")
    require(lines[end - 1] == "8", "failure event problem anchor")
    lines[end - 1] = "9"


CONTROLS = (
    ("total_as_matching_cap", "TOTAL_65_LIMIT_AFTER_ADDRESSES",
     set_solver, "literal result signature"),
    ("wrong_matching_ordinal", "TWO_CHOICES_FORWARD_CHRONOLOGY",
     set_ordinal, "literal selected step/ordinal/values"),
    ("some_zero_to_none", "ZERO_FACTOR_PRODUCT",
     lose_some_zero, "literal selected step/ordinal/values"),
    ("mul_advice_as_prerun", "FRESH_ABC",
     set_origin, "A advice provenance"),
    ("mul_advice_event_as_prerun", "FRESH_ABC",
     advice_event_as_prerun, "literal event chronology"),
    ("swap_ab_advice_events", "FRESH_ABC",
     swap_advice, "A/B advice order and provenance"),
    ("cap_with_candidate_event", "CANDIDATE_CAP",
     cap_with_candidate_event, "cap/malformed plan changed candidate work"),
    ("reverse_pending_pair", "JOINED_ROOTS",
     reverse_pair, "sorted propagation and advice order"),
    ("coordinated_checker_pc", "FRESH_ABC",
     coordinated_checker_pc, "literal phase/diagnostic/state/checker header"),
    ("wrong_product_and_image", "FRESH_ABC",
     wrong_product, "independent product and operand cells"),
    ("wrong_diagnostic_phase", "LATER_O2A_CONFLICT_PRESERVES_CHOICE",
     wrong_phase, "literal phase/diagnostic/state/checker header"),
    ("diagnostic_as_checked", "LATER_O2A_CONFLICT_PRESERVES_CHOICE",
     diagnostic_as_checked, "checker/tag presence"),
    ("wrong_failure_event_problem", "LATER_O2A_CONFLICT_PRESERVES_CHOICE",
     wrong_event_problem, "later O2a conflict lost partial diagnostic prefix"),
)


def run(data: bytes, folder: Path) -> list[dict]:
    folder.mkdir(parents=True, exist_ok=True)
    results = []
    for control, name, mutate, expected in CONTROLS:
        changed = alter(data, name, mutate)
        c_path, lean_path = folder / f"{control}.c.out", folder / f"{control}.lean.out"
        c_path.write_bytes(changed)
        lean_path.write_bytes(changed)
        try:
            verify(c_path.read_bytes(), lean_path.read_bytes())
        except RuntimeError as error:
            require(expected in str(error),
                    f"{control}: wrong rejection: {error}")
            results.append({"name": control, "target": name,
                            "rejection": str(error)})
        else:
            raise RuntimeError(f"{control}: identical wrong outputs accepted")
    changed = swap_first_two_cases(data)
    c_path = folder / "swap_case_records.c.out"
    lean_path = folder / "swap_case_records.lean.out"
    c_path.write_bytes(changed)
    lean_path.write_bytes(changed)
    try:
        verify(c_path.read_bytes(), lean_path.read_bytes())
    except RuntimeError as error:
        require("directed case order" in str(error),
                f"swap_case_records: wrong rejection: {error}")
        results.append({"name": "swap_case_records", "target": "EMPTY_PARITY",
                        "rejection": str(error)})
    else:
        raise RuntimeError("swap_case_records: identical wrong outputs accepted")
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("folder", type=Path)
    args = parser.parse_args()
    results = run(args.output.read_bytes(), args.folder)
    for item in results:
        print(f"{item['name']}: rejected at {item['target']}")
    print(f"{len(results)} identical C/Lean corruptions rejected")


if __name__ == "__main__":
    main()
