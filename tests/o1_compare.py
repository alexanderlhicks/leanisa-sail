#!/usr/bin/env python3
"""Compare complete O1 envelopes from generated C and Lean executables.

The backends receive identical typed cases from o1_cases.sail.  This parser
checks every serialized cell and event and also has independent directed
expectations, so agreement on a few status lines is insufficient.
"""

from __future__ import annotations

import argparse
import itertools
import subprocess
from pathlib import Path


# Sail enum serialization values are fixed in o1_print.sail, independently
# repeated here for directed expectations.

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

EXPECTED = [
    ("SET", 1, 3),
    ("XOR_ADVISED", 1, 3),
    ("MUL_ADVISED", 1, 3),
    ("DEREF_CELL_EQUAL", 1, 3),
    ("DEREF_CELL_ONE_UNKNOWN", 13, 1),
    ("DEREF_PC_ZERO_POINTER", 7, 0),
    ("DEREF_PC", 1, 3),
    ("DEREF_FP", 1, 3),
    ("DEREF_PC_SOURCE_ACCESS", 7, 0),
    ("DEREF_POINTER_HIGH", 9, 0),
    ("DEREF_TARGET_ACCESS_PRIORITY", 7, 0),
    ("BLAKE_ZERO", 1, 3),
    ("BLAKE_SECOND_OUTPUT_CONFLICT", 8, 0),
    ("SINGLETON_SENTINEL_ZERO_FUEL", 1, 3),
    ("ZERO_FUEL_PREFIX", 2, 2),
    ("SENTINEL_EXACT_FUEL", 1, 3),
    ("PUBLIC_CONFLICT_BEFORE_FUEL", 4, 0),
    ("ADVICE_BOUNDS_BEFORE_FUEL", 5, 0),
    ("JUMP_CHANGE_FRAME", 1, 3),
    ("JUMP_TERMINAL_BAD_FRAME", 12, 1),
    ("JUMP_FALLTHROUGH_K_GUARD", 9, 0),
    ("JUMP_FRAME_K_GUARD", 9, 0),
    ("INVALID_SHAPE_PRIORITY", 3, 0),
    ("PUBLIC_BEFORE_ADVICE", 4, 0),
    ("DUPLICATE_ADVICE", 1, 3),
    ("ADVICE_FIRST_CONFLICT", 6, 0),
    ("RAW_ZERO_ACCESS", 7, 0),
    ("BLAKE_LAST_CV_ACCESS", 7, 0),
    ("BLAKE_LAST_OUTPUT_ACCESS", 7, 0),
    ("XOR_CANCELLATION_EARLY_DEFAULT", 8, 0),
    ("MUL_EARLY_DEFAULT", 8, 0),
    ("JUMP_LATE_CONDITION", 8, 0),
    ("DEREF_CELL_BOTH_FIXED_DIFFERENT", 13, 1),
    ("DEREF_CONNECTED_PAIRS", 2, 2),
    ("DEREF_POINTER_TARGET_ALIAS", 1, 3),
    ("REPEATED_PC_PREFIX", 2, 2),
    ("FUEL_BEFORE_BAD_STEP", 2, 2),
    ("BAD_STEP_AFTER_FUEL", 7, 0),
    ("INVALID_NEXT_FETCH", 11, 0),
    ("BLAKE_HIGH_INPUT", 10, 0),
    ("BLAKE_LATE_CHUNK_GUARD", 10, 0),
    ("BLAKE_RAW_METADATA", 1, 3),
    ("BLAKE_HIGH_OUTPUT_CONFLICT", 8, 0),
    ("SET_LAST_CELL_HIGH_WORD", 1, 3),
    ("XOR_OPERAND_ALIAS", 1, 3),
    ("MUL_OPERAND_ALIAS", 1, 3),
    ("BLAKE_INPUT_ALIAS", 1, 3),
    ("BLAKE_OUTPUT_INPUT_ALIAS_CONFLICT", 8, 0),
    ("PENDING_BEFORE_BAD_FRAME", 13, 1),
]


def line(stream) -> str:
    result = stream.readline()
    if not result:
        raise AssertionError("unexpected end of canonical O1 output")
    return result.rstrip("\n")


def number(stream, base: int = 10) -> int:
    return int(line(stream), base)


def parse(path: Path):
    cases = []
    with path.open(encoding="utf-8") as stream:
        for label, expected_status, expected_tag in EXPECTED:
            require(line(stream) == label, f"case order: {label}")
            require(line(stream) == "BEGIN_O1_ENVELOPE", label)
            status, phase, tag, reason = (number(stream) for _ in range(4))
            failing_index, failing_other, steps = (number(stream) for _ in range(3))
            pc, fp = number(stream), number(stream)
            require((status, tag) == (expected_status, expected_tag), (
                label,
                status,
                tag,
            ))
            require(0 <= phase <= 10 and 0 <= reason <= 2, f"{label}: " + '0 <= phase <= 10 and 0 <= reason <= 2')
            checker_marker = line(stream)
            if checker_marker == "CHECKER":
                checker = (number(stream), number(stream), number(stream))
            else:
                require(checker_marker == "NO_CHECKER", (label, checker_marker))
                checker = None
            if tag in (2, 3):
                require(checker is not None, label)
                require(checker[:2] == (pc, fp), label)
                require(checker[2] == (5 if tag == 2 else 1), label)
            if tag == 0:
                require(checker is None, (label, "partial diagnostic has checker result"))
            if tag == 1:
                require(status in (12, 13, 14, 15), (label, status))
                require((checker is None) == (status == 13), (label, status, checker))
            if label == "JUMP_TERMINAL_BAD_FRAME":
                require(checker == (2, 2, 3), checker)
            if label == "DEREF_CELL_ONE_UNKNOWN":
                require(checker is None and reason == 1, label)
            size = number(stream)
            require(size in (2, 65536), (label, size))
            cells: list[int | None] = []
            origins: list[int] = []
            image: list[int] = []
            previous_run: tuple[int | None, int, int] | None = None
            while True:
                marker = line(stream)
                if marker == "END_CELLS":
                    break
                require(marker == "RUN", (label, marker))
                start, count = number(stream), number(stream)
                require(start == len(cells) and 1 <= count <= size - start, (
                    label,
                    start,
                    count,
                ))
                kind = line(stream)
                if kind == "UNKNOWN":
                    cell = None
                else:
                    require(kind == "FIXED", (label, kind))
                    cell = number(stream)
                origin, value = number(stream), number(stream)
                require(0 <= origin <= 6, f"{label}: " + '0 <= origin <= 6')
                require(value == (0 if cell is None else cell), (
                    label,
                    "image disagrees with partial cell",
                ))
                run = (cell, origin, value)
                require(run != previous_run, (label, "noncanonical adjacent equal runs"))
                previous_run = run
                cells.extend([cell] * count)
                origins.extend([origin] * count)
                image.extend([value] * count)
            require(len(cells) == len(origins) == len(image) == size, label)
            pairs = []
            while True:
                item = line(stream)
                if item == "END_PAIRS":
                    break
                target = int(item)
                source = number(stream)
                require(0 <= target < size and 0 <= source < size, f"{label}: " + '0 <= target < size and 0 <= source < size')
                pairs.append((target, source))
            events = []
            while True:
                item = line(stream)
                if item == "END_EVENTS":
                    break
                event = (
                    int(item),
                    number(stream),
                    number(stream),
                    number(stream),
                    number(stream),
                    number(stream),
                    number(stream),
                    number(stream),
                    number(stream),
                    number(stream),
                    number(stream),
                    number(stream),
                    number(stream),
                    number(stream),
                )
                require(0 <= event[0] <= 11 and 0 <= event[1] <= 6, f"{label}: " + '0 <= event[0] <= 11 and 0 <= event[1] <= 6')
                require(0 <= event[2] <= 10, f"{label}: " + '0 <= event[2] <= 10')
                require(event[3] <= steps and event[12] in (0, 1), f"{label}: " + 'event[3] <= steps and event[12] in (0, 1)')
                events.append(event)
            require(line(stream) == "END_O1_ENVELOPE", label)
            if tag in (2, 3):
                require(all(image[target] == image[source]
                           for target, source in pairs), label)
            if status == 13:
                unequal = next(((target, source) for target, source in pairs
                                if image[target] != image[source]), None)
                require(unequal is not None, label)
                require((failing_index, failing_other) == unequal, label)
                require(checker is None and tag == 1, label)
                expected_reason = 1 if any(cells[index] is None for index in unequal) else 2
                require(reason == expected_reason, label)
            if label == "SET":
                require(image[2] == 7 and cells[100] is None and image[100] == 0, f"{label}: " + 'image[2] == 7 and cells[100] is None and (image[100] == 0)')
                require(cells[0] == 0 and origins[0] == 2, f"{label}: " + 'cells[0] == 0 and origins[0] == 2')
                require(cells[100] is None and origins[100] == 0, f"{label}: " + 'cells[100] is None and origins[100] == 0')
            if label == "DEREF_CELL_ONE_UNKNOWN":
                require(pairs == [(3, 4)] and cells[3] is None and cells[4] == 9, f"{label}: " + 'pairs == [(3, 4)] and cells[3] is None and (cells[4] == 9)')
                require(image[3] != image[4], f"{label}: " + 'image[3] != image[4]')
            if label == "DEREF_CELL_EQUAL":
                require(pairs == [(3, 4)] and image[3] == image[4] == 9, f"{label}: " + 'pairs == [(3, 4)] and image[3] == image[4] == 9')
            if label == "DEREF_CELL_BOTH_FIXED_DIFFERENT":
                require(pairs == [(3, 4)] and reason == 2, f"{label}: " + 'pairs == [(3, 4)] and reason == 2')
                require(image[3] == 5 and image[4] == 9, f"{label}: " + 'image[3] == 5 and image[4] == 9')
            if label == "DEREF_CONNECTED_PAIRS":
                require(pairs == [(3, 4), (3, 5)] and image[3] == image[4] == image[5] == 9, f"{label}: " + 'pairs == [(3, 4), (3, 5)] and image[3] == image[4] == image[5] == 9')
            if label == "DEREF_POINTER_TARGET_ALIAS":
                require(pairs == [(2, 3)] and image[2] == image[3] == 1, f"{label}: " + 'pairs == [(2, 3)] and image[2] == image[3] == 1')
            if label == "DEREF_PC_SOURCE_ACCESS":
                require(not any(event[0] == 6 for event in events), f"{label}: " + 'not any((event[0] == 6 for event in events))')
            if label == "DEREF_POINTER_HIGH":
                require(any(event[0] == 6 and event[7] == 2 for event in events), f"{label}: " + 'any((event[0] == 6 and event[7] == 2 for event in events))')
                require(not any(event[0] == 4 for event in events), f"{label}: " + 'not any((event[0] == 4 for event in events))')
            if label == "DEREF_TARGET_ACCESS_PRIORITY":
                require(any(event[0] == 4 and event[6] == 0 for event in events), f"{label}: " + 'any((event[0] == 4 and event[6] == 0 for event in events))')
            if label == "BLAKE_SECOND_OUTPUT_CONFLICT":
                writes = [event for event in events if event[0] == 7]
                require(len(writes) == 2 and writes[0][7] == 9, f"{label}: " + 'len(writes) == 2 and writes[0][7] == 9')
                require(writes[0][12] == 1 and writes[1][7] == 10, f"{label}: " + 'writes[0][12] == 1 and writes[1][7] == 10')
                require(writes[1][12] == 0 and cells[9] is not None, f"{label}: " + 'writes[1][12] == 0 and cells[9] is not None')
                require(pc == 1 and fp == 1, f"{label}: " + 'pc == 1 and fp == 1')
            if label in ("SINGLETON_SENTINEL_ZERO_FUEL", "ZERO_FUEL_PREFIX"):
                require(not any(event[0] == 2 for event in events), f"{label}: " + 'not any((event[0] == 2 for event in events))')
            if label == "RAW_ZERO_ACCESS":
                require(any(event[0] == 4 and event[6] == 0 for event in events), f"{label}: " + 'any((event[0] == 4 and event[6] == 0 for event in events))')
            if label.startswith("BLAKE_LAST_"):
                require(not any(event[0] == 6 for event in events), f"{label}: " + 'not any((event[0] == 6 for event in events))')
            if label == "JUMP_FALLTHROUGH_K_GUARD":
                require(len([event for event in events if event[0] == 6]) == 3, f"{label}: " + 'len([event for event in events if event[0] == 6]) == 3')
                require(failing_index == 3, f"{label}: " + 'failing_index == 3')
            if label == "JUMP_FRAME_K_GUARD":
                require(failing_index == 4, f"{label}: " + 'failing_index == 4')
            if label == "REPEATED_PC_PREFIX":
                require(steps == 2 and pc == 1, f"{label}: " + 'steps == 2 and pc == 1')
                require(len([event for event in events if event[0] == 2]) == 2, f"{label}: " + 'len([event for event in events if event[0] == 2]) == 2')
            if label == "FUEL_BEFORE_BAD_STEP":
                require(steps == 1 and pc == 2, f"{label}: " + 'steps == 1 and pc == 2')
                require(not any(event[0] == 4 for event in events), f"{label}: " + 'not any((event[0] == 4 for event in events))')
            if label == "BAD_STEP_AFTER_FUEL":
                require(steps == 1 and pc == 2, f"{label}: " + 'steps == 1 and pc == 2')
                require(any(event[0] == 4 and event[6] == 0 for event in events), f"{label}: " + 'any((event[0] == 4 and event[6] == 0 for event in events))')
            if label == "INVALID_NEXT_FETCH":
                require(steps == 1 and pc != 1, f"{label}: " + 'steps == 1 and pc != 1')
            if label == "BLAKE_HIGH_INPUT":
                require(image[2] >> 128 == 1 and failing_index == 2, f"{label}: " + 'image[2] >> 128 == 1 and failing_index == 2')
            if label == "BLAKE_LATE_CHUNK_GUARD":
                require(image[7] >> 128 == 1 and failing_index == 7, f"{label}: " + 'image[7] >> 128 == 1 and failing_index == 7')
            if label == "BLAKE_HIGH_OUTPUT_CONFLICT":
                require(cells[9] is not None and cells[9] >> 128 == 1, f"{label}: " + 'cells[9] is not None and cells[9] >> 128 == 1')
            if label == "SET_LAST_CELL_HIGH_WORD":
                require(image[65535] == int(
                    "0123456789abcdef00000000000000000000000000000007", 16
                ), f"{label}: " + "image[65535] == int('0123456789abcdef00000000000000000000000000000007', 16)")
                require(cells[65535] == image[65535], f"{label}: " + 'cells[65535] == image[65535]')
            if label == "PENDING_BEFORE_BAD_FRAME":
                require((pc, fp) == (8, 2) and checker is None, f"{label}: " + '(pc, fp) == (8, 2) and checker is None')
                require(pairs == [(3, 4)] and reason == 1, f"{label}: " + 'pairs == [(3, 4)] and reason == 1')
            observations = [(event[3], event[7]) for event in events if event[0] == 6]
            if label in ("XOR_ADVISED", "MUL_ADVISED"):
                require(observations == [(0, 2), (0, 3)], (label, observations))
            if label in ("XOR_OPERAND_ALIAS", "MUL_OPERAND_ALIAS"):
                require(observations == [(0, 2), (0, 2)], (label, observations))
            if label == "JUMP_CHANGE_FRAME":
                require(observations == [(0, 2), (0, 3), (0, 4),
                                        (1, 5), (1, 6), (1, 7)], f"{label}: " + 'observations == [(0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (1, 7)]')
            if label in ("JUMP_FALLTHROUGH_K_GUARD", "JUMP_FRAME_K_GUARD"):
                require(observations == [(0, 2), (0, 3), (0, 4)], f"{label}: " + 'observations == [(0, 2), (0, 3), (0, 4)]')
            if label in ("BLAKE_ZERO", "BLAKE_RAW_METADATA",
                         "BLAKE_HIGH_INPUT", "BLAKE_LATE_CHUNK_GUARD"):
                require(observations == [(0, index) for index in (2, 3, 4, 5, 6, 7, 8)], f"{label}: " + 'observations == [(0, index) for index in (2, 3, 4, 5, 6, 7, 8)]')
            if label == "BLAKE_INPUT_ALIAS":
                require(observations == [(0, index) for index in (2, 2, 2, 2, 4, 5, 2)], f"{label}: " + 'observations == [(0, index) for index in (2, 2, 2, 2, 4, 5, 2)]')
            if label == "BLAKE_OUTPUT_INPUT_ALIAS_CONFLICT":
                require(observations == [(0, index) for index in (2, 3, 4, 5, 6, 7, 8)], f"{label}: " + 'observations == [(0, index) for index in (2, 3, 4, 5, 6, 7, 8)]')
                writes = [event for event in events if event[0] == 7]
                require(len(writes) == 1 and writes[0][7] == 2, f"{label}: " + 'len(writes) == 1 and writes[0][7] == 2')
                require(writes[0][12] == 0 and failing_index == 2, f"{label}: " + 'writes[0][12] == 0 and failing_index == 2')
                require(cells[2] == 0 and origins[2] == 5 and pc == 1, f"{label}: " + 'cells[2] == 0 and origins[2] == 5 and (pc == 1)')
            if label.endswith("EARLY_DEFAULT") or label == "JUMP_LATE_CONDITION":
                require(any(event[0] == 5 and event[7] == 2 for event in events), 'O1 trailer: any((event[0] == 5 and event[7] == 2 for event in events))')
                require(pc == 2 and steps == 1, 'O1 trailer: pc == 2 and steps == 1')
            cases.append((label, status, tag, len(pairs), len(events)))
        require(line(stream) == "O1 CASES PASS", "O1 trailer: line(stream) == 'O1 CASES PASS'")
        require(stream.read() == "", "unexpected trailing output")
    return cases


def run(binary: Path, output: Path, timeout: int):
    with output.open("w", encoding="utf-8") as stream:
        subprocess.run([str(binary)], check=True, stdout=stream, timeout=timeout)


def compare_files(left: Path, right: Path):
    with left.open(encoding="utf-8") as a, right.open(encoding="utf-8") as b:
        for index, (x, y) in enumerate(itertools.zip_longest(a, b), 1):
            if x != y:
                raise AssertionError(f"C/Lean envelope mismatch at line {index}: {x!r} != {y!r}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("c_binary", type=Path)
    parser.add_argument("lean_binary", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    c_output, lean_output = args.out / "c.out", args.out / "lean.out"
    run(args.c_binary, c_output, args.timeout)
    run(args.lean_binary, lean_output, args.timeout)
    compare_files(c_output, lean_output)
    cases = parse(c_output)
    require(parse(lean_output) == cases, 'O1 C/Lean comparison: parse(lean_output) == cases')
    print(f"O1 full-envelope comparison: {len(cases)} cases PASS")


if __name__ == "__main__":
    main()
