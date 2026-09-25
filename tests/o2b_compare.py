#!/usr/bin/env python3
"""Parse the entire O2b C/Lean envelope and apply independent literal checks."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
from o2b_oracle import choose, emul

U64 = (1 << 64) - 1
U192 = (1 << 192) - 1
SIZE = 65536
EXPECTED_ORDER = """EMPTY_PARITY UNEXECUTED_PARITY FRESH_ABC
    CANDIDATE_EXHAUSTION_PURE SECOND_CANDIDATE ALIAS_A_B ALIAS_A_B_REJECT
    ALIAS_C_A ALIAS_ALL ALIAS_ALL_REJECT JOINED_ROOTS
    JOINED_ROOT_CONFLICT_PURE ONE_MISSING_FACTOR FIXED_FACTORS_NOT_TARGETS
    ADDRESS_BEFORE_MALFORMED LONG_LIST_FIRST_ADDRESS_PRIORITY
    THIRD_ADDRESS_FAILURE LONG_LIST_THIRD_ADDRESS_PRIORITY
    MALFORMED_FETCHED_PLAN CANDIDATE_CAP NONMATCHING_NOT_COUNTED
    TOTAL_64_NO_MATCH_PARITY TOTAL_65_LIMIT_AFTER_ADDRESSES
    FIRST_BAD_ADDRESS_BEATS_65 SECOND_BAD_ADDRESS_BEATS_65
    THIRD_BAD_ADDRESS_BEATS_65 MATCHING_9_AT_TOTAL_64
    TOTAL_65_BEATS_MATCHING_9 MATCHING_8_AT_TOTAL_64 FUTURE_MALFORMED_INERT
    MATCHING_CAP_BEATS_MALFORMED NONMUL_IGNORES_65 FUEL_IGNORES_65
    PUBLIC_CONFLICT_IGNORES_65 ADVICE_FAILURE_IGNORES_65 SENTINEL_IGNORES_65
    ALIAS_C_B ALIAS_C_B_REJECT ZERO_FACTOR_PRODUCT HIGH_BIT_REDUCTION_PRODUCT
    DYNAMIC_STEP_NOT_PC TWO_CHOICES_FORWARD_CHRONOLOGY
    LATER_DIAGNOSTIC_PRESERVES_CHOICE_CHRONOLOGY SHAPE_FAILURE_IGNORES_65
    ORDERED_ADVICE_CONFLICT_IGNORES_65 FETCH_FAILURE_IGNORES_65
    LATER_O2A_CONFLICT_PRESERVES_CHOICE""".split()


def require(ok: bool, why: str) -> None:
    if not ok:
        raise RuntimeError(why)


class Cursor:
    def __init__(self, data: bytes):
        require(data.endswith(b"\n") and b"\r" not in data,
                "stream: missing final newline or CR byte")
        self.lines = data.decode("utf-8").split("\n")[:-1]
        self.pos = 0

    def take(self) -> str:
        require(self.pos < len(self.lines), "stream: truncated envelope")
        value = self.lines[self.pos]
        self.pos += 1
        return value

    def expect(self, marker: str) -> None:
        got = self.take()
        require(got == marker, f"stream: expected {marker}, got {got!r}")

    def uint(self, maximum: int, label: str) -> int:
        token = self.take()
        require(re.fullmatch(r"(?:0|[1-9][0-9]*)", token) is not None,
                f"{label}: noncanonical decimal {token!r}")
        value = int(token)
        require(value <= maximum, f"{label}: out of range")
        return value

    def done(self) -> bool:
        return self.pos == len(self.lines)


def parse_option(c: Cursor, label: str) -> int | None:
    marker = c.take()
    if marker == "NONE":
        return None
    require(marker == "SOME", f"{label}: option marker")
    return c.uint(U192, label)


def parse_common(c: Cursor, name: str) -> dict:
    c.expect("BEGIN_O2a_ENVELOPE")
    status = c.uint(17, f"{name}: status")
    phase = c.uint(10, f"{name}: phase")
    tag = c.uint(3, f"{name}: tag")
    reason = c.uint(2, f"{name}: pending reason")
    fi = c.uint(1 << 32, f"{name}: failing index")
    fo = c.uint(1 << 32, f"{name}: failing other")
    steps = c.uint(1 << 32, f"{name}: steps")
    pc = c.uint(U64, f"{name}: pc")
    fp = c.uint(U64, f"{name}: fp")
    checker_marker = c.take()
    if checker_marker == "NO_CHECKER":
        checker = None
    else:
        require(checker_marker == "CHECKER", f"{name}: checker marker")
        checker = (c.uint(U64, f"{name}: checker pc"),
                   c.uint(U64, f"{name}: checker fp"),
                   c.uint(5, f"{name}: checker verdict"))
    size = c.uint(1 << 32, f"{name}: memory size")
    require(size == SIZE, f"{name}: memory size is not {SIZE}")
    runs = []
    covered = 0
    while True:
        marker = c.take()
        if marker == "END_CELLS":
            break
        require(marker == "RUN", f"{name}: cell run marker")
        start = c.uint(SIZE, f"{name}: run start")
        count = c.uint(SIZE, f"{name}: run count")
        kind = c.take()
        if kind == "UNKNOWN":
            value = None
        else:
            require(kind == "FIXED", f"{name}: cell kind")
            value = c.uint(U192, f"{name}: cell value")
        origin = c.uint(9, f"{name}: origin")
        image = c.uint(U192, f"{name}: image")
        require(start == covered and count > 0 and covered + count <= SIZE,
                f"{name}: cell-run coverage")
        require(image == (0 if value is None else value),
                f"{name}: image inconsistent with cell")
        require(not runs or runs[-1][2:] != (value, origin, image),
                f"{name}: adjacent equal cell runs")
        runs.append((start, count, value, origin, image))
        covered += count
    require(covered == SIZE, f"{name}: incomplete cell coverage")
    pairs = []
    while True:
        marker = c.take()
        if marker == "END_PAIRS":
            break
        require(re.fullmatch(r"(?:0|[1-9][0-9]*)", marker) is not None,
                f"{name}: noncanonical pending pair target")
        target = int(marker)
        source = c.uint(SIZE - 1, f"{name}: pending pair source")
        require(target < SIZE, f"{name}: pending pair target range")
        pairs.append((target, source))
    events = []
    previous_step = 0
    while True:
        marker = c.take()
        if marker == "END_EVENTS":
            break
        require(re.fullmatch(r"(?:0|[1-9][0-9]*)", marker) is not None,
                f"{name}: noncanonical event kind")
        kind = int(marker)
        require(kind <= 13, f"{name}: event kind range")
        event = (kind, c.uint(6, f"{name}: event opcode"),
                 c.uint(10, f"{name}: event phase"),
                 c.uint(1 << 32, f"{name}: event step"),
                 c.uint(U64, f"{name}: event pc"),
                 c.uint(U64, f"{name}: event fp"),
                 c.uint(U64, f"{name}: event address"),
                 c.uint(1 << 32, f"{name}: event index"),
                 c.uint(1 << 32, f"{name}: event other"),
                 c.uint(U192, f"{name}: event value"),
                 c.uint(U192, f"{name}: event previous"),
                 c.uint(9, f"{name}: event origin"),
                 c.uint(1, f"{name}: event success"),
                 c.uint(17, f"{name}: event problem"))
        require(previous_step <= event[3] <= steps,
                f"{name}: event step chronology")
        previous_step = event[3]
        events.append(event)
    c.expect("END_O2a_ENVELOPE")

    require((tag == 0) == (checker is None) or
            (tag == 1 and checker is None),
            f"{name}: checker/tag presence")
    if tag == 2:
        require(status == 2 and checker == (pc, fp, 5),
                f"{name}: checked prefix consistency")
    elif tag == 3:
        require(status == 1 and checker == (pc, fp, 1),
                f"{name}: checked halt consistency")
    elif tag == 1 and checker is not None:
        require(status in (12, 14, 15),
                f"{name}: diagnostic complete checker status")
        if status == 12:
            require(checker == (pc, fp, 3),
                    f"{name}: terminal-frame checker result")
    return dict(status=status, phase=phase, tag=tag, reason=reason,
                fi=fi, fo=fo, steps=steps, pc=pc, fp=fp,
                checker=checker, size=size, runs=runs, pairs=pairs,
                events=events)


def parse(data: bytes) -> list[dict]:
    c = Cursor(data)
    cases = []
    seen = set()
    while not c.done():
        name = c.take()
        require(re.fullmatch(r"[A-Z][A-Z0-9_]*", name) is not None and
                name not in seen, f"case: invalid or repeated label {name!r}")
        seen.add(name)
        c.expect("BEGIN_O2b_ENVELOPE")
        solver = c.uint(5, f"{name}: solver status")
        count = c.uint(1 << 32, f"{name}: choice count")
        choices = []
        for _ in range(count):
            c.expect("CHOICE")
            step = c.uint(1 << 32, f"{name}: choice step")
            ordinal = c.uint(7, f"{name}: matching ordinal")
            a = parse_option(c, f"{name}: choice A")
            b = parse_option(c, f"{name}: choice B")
            require(a is not None or b is not None,
                    f"{name}: malformed committed choice")
            require(not choices or choices[-1][0] < step,
                    f"{name}: choice chronology")
            choices.append((step, ordinal, a, b))
        c.expect("END_CHOICES")
        common = parse_common(c, name)
        c.expect("END_O2b_ENVELOPE")
        require(all(step < common["steps"] for step, _, _, _ in choices),
                f"{name}: choice beyond committed steps")
        if solver != 0:
            require(common["tag"] == 0 and common["checker"] is None,
                    f"{name}: solver diagnostic received checked tag")
        cases.append(dict(name=name, solver=solver, choices=choices,
                          **common))
    return cases


def cell(case: dict, index: int) -> tuple[int | None, int, int]:
    require(0 <= index < SIZE, "cell index out of range")
    for start, count, value, origin, image in case["runs"]:
        if start <= index < start + count:
            return (value, origin, image)
    raise RuntimeError(f"{case['name']}: missing cell {index}")


def event_kinds(case: dict) -> list[int]:
    return [event[0] for event in case["events"]]


def verify(c_data: bytes, lean_data: bytes) -> list[dict]:
    require(c_data == lean_data, "C/Lean complete O2b bytes differ")
    cases = parse(c_data)
    check_literals(cases)
    return cases


def verify_checker_control(c_data: bytes, lean_data: bytes) -> dict:
    require(c_data == lean_data, "C/Lean checker-control bytes differ")
    cases = parse(c_data)
    require(len(cases) == 1 and
            cases[0]["name"] == "SYNTHETIC_CHECKER_REJECTION_AFTER_COMMIT",
            "synthetic checker-control case count/name")
    case = cases[0]
    require((case["solver"], case["status"], case["phase"], case["tag"],
             case["steps"], case["pc"], case["fp"], case["checker"],
             case["choices"]) ==
            (0, 14, 10, 1, 1, 2, 1, (2, 1, 1), [(0, 0, 2, 3)]),
            "synthetic checker-control literal header and choice")
    require([cell(case, i) for i in (3, 4, 5)] ==
            [(2, 9, 2), (3, 9, 3), (6, 6, 6)] and
            event_kinds(case) == [2, 3, 3, 3, 13, 13, 6, 6, 7, 9, 10] and
            case["events"][-1][13] == 14,
            "synthetic checker-control committed prefix and rejection")
    return case


def check_literals(cases: list[dict]) -> None:
    groups = {
        (0, 1, 3, 1): """EMPTY_PARITY UNEXECUTED_PARITY FRESH_ABC SECOND_CANDIDATE
            ALIAS_A_B ALIAS_C_A ALIAS_ALL ONE_MISSING_FACTOR
            NONMATCHING_NOT_COUNTED TOTAL_64_NO_MATCH_PARITY MATCHING_8_AT_TOTAL_64
            FUTURE_MALFORMED_INERT NONMUL_IGNORES_65 ALIAS_C_B
            ZERO_FACTOR_PRODUCT HIGH_BIT_REDUCTION_PRODUCT""",
        (1, 0, 0, 0): """CANDIDATE_EXHAUSTION_PURE ALIAS_A_B_REJECT
            ALIAS_ALL_REJECT FIXED_FACTORS_NOT_TARGETS ALIAS_C_B_REJECT""",
        (0, 2, 2, 2): "JOINED_ROOTS TWO_CHOICES_FORWARD_CHRONOLOGY",
        (1, 0, 0, 1): "JOINED_ROOT_CONFLICT_PURE",
        (0, 7, 0, 0): """ADDRESS_BEFORE_MALFORMED LONG_LIST_FIRST_ADDRESS_PRIORITY
            THIRD_ADDRESS_FAILURE LONG_LIST_THIRD_ADDRESS_PRIORITY
            FIRST_BAD_ADDRESS_BEATS_65 SECOND_BAD_ADDRESS_BEATS_65
            THIRD_BAD_ADDRESS_BEATS_65""",
        (2, 0, 0, 0): "MALFORMED_FETCHED_PLAN",
        (3, 0, 0, 0): "CANDIDATE_CAP MATCHING_9_AT_TOTAL_64 MATCHING_CAP_BEATS_MALFORMED",
        (4, 0, 0, 0): "TOTAL_65_LIMIT_AFTER_ADDRESSES TOTAL_65_BEATS_MATCHING_9",
        (0, 2, 2, 0): "FUEL_IGNORES_65",
        (0, 4, 0, 0): "PUBLIC_CONFLICT_IGNORES_65",
        (0, 5, 0, 0): "ADVICE_FAILURE_IGNORES_65",
        (0, 1, 3, 0): "SENTINEL_IGNORES_65",
        (2, 0, 0, 2): "DYNAMIC_STEP_NOT_PC LATER_DIAGNOSTIC_PRESERVES_CHOICE_CHRONOLOGY",
        (0, 3, 0, 0): "SHAPE_FAILURE_IGNORES_65",
        (0, 6, 0, 0): "ORDERED_ADVICE_CONFLICT_IGNORES_65",
        (0, 11, 0, 1): "FETCH_FAILURE_IGNORES_65",
        (0, 8, 0, 1): "LATER_O2A_CONFLICT_PRESERVES_CHOICE",
    }
    expected = {name: signature for signature, names in groups.items()
                for name in names.split()}
    require(len(expected) == 47 and len(cases) == 47,
            "directed case count and distinct oracle names")
    require([case["name"] for case in cases] == EXPECTED_ORDER,
            "directed case order")
    require(set(expected) == {case["name"] for case in cases},
            "directed case names")
    by = {case["name"]: case for case in cases}
    for name, signature in expected.items():
        case = by[name]
        actual = tuple(case[key] for key in ("solver", "status", "tag", "steps"))
        require(actual == signature, f"{name}: literal result signature {actual}")
    address_failures = {
        "ADDRESS_BEFORE_MALFORMED", "LONG_LIST_FIRST_ADDRESS_PRIORITY",
        "THIRD_ADDRESS_FAILURE", "LONG_LIST_THIRD_ADDRESS_PRIORITY",
        "FIRST_BAD_ADDRESS_BEATS_65", "SECOND_BAD_ADDRESS_BEATS_65",
        "THIRD_BAD_ADDRESS_BEATS_65",
    }
    for name, case in by.items():
        phase = (5 if name in address_failures else
                 1 if name in ("ADVICE_FAILURE_IGNORES_65",
                               "ORDERED_ADVICE_CONFLICT_IGNORES_65") else
                 4 if name == "FETCH_FAILURE_IGNORES_65" else
                 8 if name == "LATER_O2A_CONFLICT_PRESERVES_CHOICE" else 0)
        failing_index = (65536 if name == "ADVICE_FAILURE_IGNORES_65" else
                         3 if name in ("ORDERED_ADVICE_CONFLICT_IGNORES_65",
                                       "LATER_O2A_CONFLICT_PRESERVES_CHOICE")
                         else 0)
        pc = (32 if name == "FETCH_FAILURE_IGNORES_65" else
              4 if name in ("JOINED_ROOTS", "TWO_CHOICES_FORWARD_CHRONOLOGY",
                            "LATER_DIAGNOSTIC_PRESERVES_CHOICE_CHRONOLOGY") else
              1 if case["steps"] == 0 or name == "DYNAMIC_STEP_NOT_PC" else 2)
        checker = ((pc, 1, 1) if case["tag"] == 3 else
                   (pc, 1, 5) if case["tag"] == 2 else None)
        require((case["phase"], case["reason"], case["fi"], case["fo"],
                 case["pc"], case["fp"], case["checker"]) ==
                (phase, 0, failing_index, 0, pc, 1, checker),
                f"{name}: literal phase/diagnostic/state/checker header")

    selected = {
        "FRESH_ABC": [(0, 0, 2, 3)],
        "SECOND_CANDIDATE": [(0, 1, 1, 7)],
        "ALIAS_A_B": [(0, 0, 2, 2)],
        "ALIAS_C_A": [(0, 0, 2, 1)],
        "ALIAS_ALL": [(0, 0, 1, None)],
        "JOINED_ROOTS": [(1, 0, 2, None)],
        "ONE_MISSING_FACTOR": [(0, 0, 2, None)],
        "NONMATCHING_NOT_COUNTED": [(0, 0, 2, 3)],
        "MATCHING_8_AT_TOTAL_64": [(0, 0, 2, 3)],
        "FUTURE_MALFORMED_INERT": [(0, 0, 2, 3)],
        "ALIAS_C_B": [(0, 0, 1, 3)],
        "ZERO_FACTOR_PRODUCT": [(0, 0, 0, 3)],
        "HIGH_BIT_REDUCTION_PRODUCT": [(0, 0, 1 << 63, 2)],
        "DYNAMIC_STEP_NOT_PC": [(0, 0, 2, 3)],
        "TWO_CHOICES_FORWARD_CHRONOLOGY": [(0, 0, 2, 3), (1, 1, 2, 3)],
        "LATER_DIAGNOSTIC_PRESERVES_CHOICE_CHRONOLOGY":
            [(0, 0, 2, 3), (1, 1, 2, 3)],
        "LATER_O2A_CONFLICT_PRESERVES_CHOICE": [(0, 0, 2, 3)],
    }
    for case in cases:
        require(case["choices"] == selected.get(case["name"], []),
                f"{case['name']}: literal selected step/ordinal/values")

    # A separate polynomial implementation establishes actual products,
    # including the high-bit reduction that native integer multiply misses.
    require(emul(2, 3) == 6 and emul(2, 2) == 4 and
            emul(1 << 63, 2) == 27, "independent product constants")
    products = {
        "FRESH_ABC": (3, 4, 5, 2, 3, 6),
        "SECOND_CANDIDATE": (3, 4, 5, 1, 7, 7),
        "ALIAS_A_B": (3, 3, 5, 2, 2, 4),
        "ALIAS_C_A": (3, 4, 3, 2, 1, 2),
        "ALIAS_ALL": (3, 3, 3, 1, 1, 1),
        "ALIAS_C_B": (3, 4, 4, 1, 3, 3),
        "ZERO_FACTOR_PRODUCT": (3, 4, 5, 0, 3, 0),
        "HIGH_BIT_REDUCTION_PRODUCT": (3, 4, 5, 1 << 63, 2, 27),
    }
    for name, (ia, ib, ic, a, b, product) in products.items():
        case = by[name]
        require(emul(a, b) == product and cell(case, ia)[0] == a and
                cell(case, ib)[0] == b and cell(case, ic)[0] == product,
                f"{name}: independent product and operand cells")
        require(cell(case, ia)[1] == 9,
                f"{name}: A advice provenance")
        if ib != ia:
            require(cell(case, ib)[1] == 9,
                    f"{name}: B advice provenance")
    require(cell(by["FRESH_ABC"], 5) == (6, 6, 6),
            "FRESH_ABC: literal output origin/image")
    require(cell(by["HIGH_BIT_REDUCTION_PRODUCT"], 5) == (27, 6, 27),
            "HIGH_BIT_REDUCTION_PRODUCT: literal reduced output")
    require(cell(by["TWO_CHOICES_FORWARD_CHRONOLOGY"], 8) == (6, 1, 6),
            "TWO_CHOICES_FORWARD_CHRONOLOGY: fixed output")

    root_cases = {
        "FRESH_ABC": ((3, 4, 5), {}, [(2, 3)], 0),
        "ALIAS_A_B": ((3, 3, 5), {}, [(2, 2)], 0),
        "ALIAS_A_B_REJECT": ((3, 3, 5), {}, [(2, 3)], None),
        "ALIAS_C_A": ((3, 4, 3), {}, [(2, 1)], 0),
        "ALIAS_ALL": ((3, 3, 3), {}, [(1, None)], 0),
        "ALIAS_ALL_REJECT": ((3, 3, 3), {}, [(2, None)], None),
        "ALIAS_C_B": ((3, 4, 4), {}, [(1, 3)], 0),
        "ALIAS_C_B_REJECT": ((3, 4, 4), {}, [(2, 3)], None),
        "SECOND_CANDIDATE": ((3, 4, 5), {5: 7}, [(2, 3), (1, 7)], 1),
    }
    for name, (roots, fixed, plans, ordinal) in root_cases.items():
        predicted = choose(roots, fixed, plans)
        require((None if predicted is None else predicted[0]) == ordinal,
                f"{name}: independent virtual-root candidate selection")
        require((None if predicted is None else predicted[0]) ==
                (None if not by[name]["choices"] else by[name]["choices"][0][1]),
                f"{name}: selected ordinal disagrees with oracle")

    def kinds(name: str) -> list[int]:
        return event_kinds(by[name])

    require(kinds("FRESH_ABC") ==
            [0, 0, 2, 3, 3, 3, 13, 13, 6, 6, 7, 9],
            "FRESH_ABC: literal event chronology")
    fresh = by["FRESH_ABC"]["events"]
    require([(e[7], e[9], e[11]) for e in fresh if e[0] == 13] ==
            [(3, 2, 9), (4, 3, 9)],
            "FRESH_ABC: A/B advice order and provenance")
    require([(e[7], e[9]) for e in fresh if e[0] == 6] == [(3, 2), (4, 3)],
            "FRESH_ABC: A/B observation order")
    require([(e[7], e[9], e[11]) for e in fresh if e[0] == 7] == [(5, 6, 6)],
            "FRESH_ABC: actual output event")
    for name in ("CANDIDATE_EXHAUSTION_PURE", "ALIAS_A_B_REJECT",
                 "ALIAS_ALL_REJECT", "JOINED_ROOT_CONFLICT_PURE",
                 "ALIAS_C_B_REJECT"):
        require(13 not in kinds(name) and 5 not in kinds(name) and
                cell(by[name], 3)[0] is None,
                f"{name}: rejected preflight changed candidate work")
    for name in ("TOTAL_65_LIMIT_AFTER_ADDRESSES",
                 "TOTAL_65_BEATS_MATCHING_9"):
        require(kinds(name) == [0, 0, 2, 3, 3, 3] and
                cell(by[name], 3) == (None, 0, 0),
                f"{name}: total limit must precede candidate effects")
    for name in ("CANDIDATE_CAP", "MATCHING_9_AT_TOTAL_64",
                 "MATCHING_CAP_BEATS_MALFORMED", "MALFORMED_FETCHED_PLAN"):
        require(kinds(name) == [0, 0, 2, 3, 3, 3] and
                cell(by[name], 3) == (None, 0, 0) and
                cell(by[name], 4) == (None, 0, 0) and
                cell(by[name], 5) == (None, 0, 0),
                f"{name}: cap/malformed plan changed candidate work")
    for index, name in enumerate(("FIRST_BAD_ADDRESS_BEATS_65",
                                  "SECOND_BAD_ADDRESS_BEATS_65",
                                  "THIRD_BAD_ADDRESS_BEATS_65")):
        require(kinds(name) == [0, 0, 2] + [3] * index + [4, 10],
                f"{name}: architectural address priority")
    require(by["JOINED_ROOTS"]["pairs"] == [(3, 4)] and
            cell(by["JOINED_ROOTS"], 4) == (2, 7, 2) and
            [(e[0], e[7], e[11]) for e in by["JOINED_ROOTS"]["events"]
             if e[0] in (12, 13)] == [(13, 3, 9), (12, 4, 7)],
            "JOINED_ROOTS: sorted propagation and advice order")
    for name in ("EMPTY_PARITY", "UNEXECUTED_PARITY",
                 "TOTAL_64_NO_MATCH_PARITY"):
        common = {k: v for k, v in by[name].items()
                  if k not in ("name", "solver", "choices")}
        baseline = {k: v for k, v in by["EMPTY_PARITY"].items()
                    if k not in ("name", "solver", "choices")}
        require(common == baseline, f"{name}: complete no-match O2a parity")
    require(by["TWO_CHOICES_FORWARD_CHRONOLOGY"]["choices"] ==
            by["LATER_DIAGNOSTIC_PRESERVES_CHOICE_CHRONOLOGY"]["choices"],
            "later diagnostic changed committed choice chronology")
    later = by["LATER_O2A_CONFLICT_PRESERVES_CHOICE"]
    require(later["checker"] is None and later["tag"] == 0 and
            cell(later, 5) == (6, 6, 6) and later["events"][-1][13] == 8,
            "later O2a conflict lost partial diagnostic prefix")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("c", type=Path)
    parser.add_argument("lean", type=Path)
    parser.add_argument("--dump", action="store_true")
    args = parser.parse_args()
    cases = verify(args.c.read_bytes(), args.lean.read_bytes())
    if args.dump:
        for case in cases:
            print(json.dumps({key: case[key] for key in
                ("name", "solver", "choices", "status", "phase", "tag",
                 "reason", "fi", "fo", "steps", "pc", "fp", "checker",
                 "pairs")}))
    print(f"{len(cases)} complete O2b envelopes parsed; C/Lean bytes equal")


if __name__ == "__main__":
    main()
