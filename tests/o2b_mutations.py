#!/usr/bin/env python3
"""Generate single-change O2b source mutants from unique public anchors."""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "spec/o2b_candidate.sail"

# Each target is the first directed case whose assertion or literal oracle
# must reject the mutant. A compiler failure is never a successful detector.
MUTATIONS = {
    "scan_before_addresses": (
        "      let ra = o2a_resolve(w, index, kmul(w.registers.fp, a)); w = ra.work;",
        "      let scan = o2b_scan_fuel(plans, w.steps, 64, 0, [||]);\n"
        "      if scan.status == O2bScanLimit then return struct { work = w,\n"
        "        solver = O2bPlanListLimit, choice = None() };\n"
        "      let ra = o2a_resolve(w, index, kmul(w.registers.fp, a)); w = ra.work;",
        "LONG_LIST_FIRST_ADDRESS_PRIORITY",
    ),
    "fuel_63": (
        "let scan = o2b_scan_fuel(plans, w.steps, 64, 0, [||]);",
        "let scan = o2b_scan_fuel(plans, w.steps, 63, 0, [||]);",
        "TOTAL_64_NO_MATCH_PARITY",
    ),
    "fuel_65": (
        "let scan = o2b_scan_fuel(plans, w.steps, 64, 0, [||]);",
        "let scan = o2b_scan_fuel(plans, w.steps, 65, 0, [||]);",
        "TOTAL_65_LIMIT_AFTER_ADDRESSES",
    ),
    "match_cap_7": (
        "if scan.matching_count > 8 then return",
        "if scan.matching_count > 7 then return",
        "MATCHING_8_AT_TOTAL_64",
    ),
    "match_cap_9": (
        "if scan.matching_count > 8 then return",
        "if scan.matching_count > 9 then return",
        "CANDIDATE_CAP",
    ),
    "total_as_match_cap": (
        "solver = O2bPlanListLimit, choice = None() };",
        "solver = O2bCandidateCap, choice = None() };",
        "TOTAL_65_LIMIT_AFTER_ADDRESSES",
    ),
    "matching_before_total": (
        "      if scan.status == O2bScanLimit then return struct { work = w,\n"
        "        solver = O2bPlanListLimit, choice = None() };\n"
        "      if scan.matching_count > 8 then return struct { work = w,\n"
        "        solver = O2bCandidateCap, choice = None() };",
        "      if scan.matching_count > 8 then return struct { work = w,\n"
        "        solver = O2bCandidateCap, choice = None() };\n"
        "      if scan.status == O2bScanLimit then return struct { work = w,\n"
        "        solver = O2bPlanListLimit, choice = None() };",
        "TOTAL_65_BEATS_MATCHING_9",
    ),
    "step_as_pc": (
        "o2b_scan_fuel(plans, w.steps, 64, 0, [||])",
        "o2b_scan_fuel(plans, unsigned(w.registers.pc), 64, 0, [||])",
        "FRESH_ABC",
    ),
    "malformed_original_list": (
        "if o2b_malformed(candidates) then return",
        "if o2b_malformed(plans) then return",
        "FUTURE_MALFORMED_INERT",
    ),
    "retain_reverse_omitted": (
        "let candidates = o2b_reverse_plans(scan.matches_reverse);",
        "let candidates = scan.matches_reverse;",
        "SECOND_CANDIDATE",
    ),
    "choice_reverse_omitted": (
        "choices = o2b_reverse_choices(choices)",
        "choices = choices",
        "TWO_CHOICES_FORWARD_CHRONOLOGY",
    ),
    "eager_after_rejected_trials": (
        "work = if picked.status == O2bInternal then o2b_internalize(w) else w,",
        "work = if picked.status == O2bInternal then o2b_internalize(w) else o2a_observe(w, ia),",
        "CANDIDATE_EXHAUSTION_PURE",
    ),
    "split_joined_root": (
        "Some(struct { key = root.key, fixed = false,",
        "Some(struct { key = index, fixed = false,",
        "JOINED_ROOT_CONFLICT_PURE",
    ),
    "observe_b_before_a": (
        "          w = o2a_observe(w, ia);\n"
        "          w = o2a_observe(w, ib);",
        "          w = o2a_observe(w, ib);\n"
        "          w = o2a_observe(w, ia);",
        "FRESH_ABC",
    ),
    "prerun_advice_origin": (
        "Some(value) => w = o2a_assign(w, ia, value, O2bMulAdvice,",
        "Some(value) => w = o2a_assign(w, ia, value, O2aAdvice,",
        "FRESH_ABC",
    ),
    "wrong_mul_output": (
        "emul(o2a_value(w, ia), o2a_value(w, ib)), O2aOutput,",
        "sail_zeros(192), O2aOutput,",
        "FRESH_ABC",
    ),
    "native_mul_output": (
        "emul(o2a_value(w, ia), o2a_value(w, ib)), O2aOutput,",
        "get_slice_int(192, unsigned(o2a_value(w, ia)) * unsigned(o2a_value(w, ib)), 0), O2aOutput,",
        "HIGH_BIT_REDUCTION_PRODUCT",
    ),
    "ignore_fixed_product": (
        "Some(v) => if v == product then O2bTrialPass else O2bTrialReject,",
        "Some(v) => O2bTrialPass,",
        "CANDIDATE_EXHAUSTION_PURE",
    ),
    "diagnostic_checked_tag": (
        "o2a_pack(w, O2aDiagnosticPartial, None()), stepped.solver, choices);",
        "o2a_pack(w, O2aCheckedHalted, None()), stepped.solver, choices);",
        "CANDIDATE_EXHAUSTION_PURE",
    ),
    "checker_bypass": (
        "o2a_complete(w, program, public_input, fuel, verdict)",
        "o2a_pack(w, O2aDiagnosticPartial, None())",
        "EMPTY_PARITY",
    ),
}


def generate(folder: Path) -> None:
    folder.mkdir(parents=True, exist_ok=True)
    source = SOURCE.read_text()
    for name, (old, new, _) in MUTATIONS.items():
        count = source.count(old)
        if count != 1:
            raise RuntimeError(f"{name}: source anchor count {count}")
        (folder / f"{name}.sail").write_text(source.replace(old, new, 1))
