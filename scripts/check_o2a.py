#!/usr/bin/env python3
"""Validate the accepted equality-only O2a runner in C and extracted Lean.

The slow runner is a test-only reference control for the sparse runner.
This gate makes no MUL-advice, inverse, or formal runner-to-policy bridge claim.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BASE = (
    "spec/field.sail", "spec/blake2s.sail", "spec/machine.sail",
    "spec/forward.sail",
)
SPARSE = BASE + ("spec/o2a_sparse_map.sail", "spec/o2a_sparse_runner.sail")
SLOW = BASE + ("tests/o2a_slow_control.sail",)
SUITES = {
    "directed": ("tests/o2a_cases.sail", "tests/o2a_cases_slow.sail", 12),
    "extra": ("tests/o2a_extra.sail", "tests/o2a_extra_slow.sail", 14),
}
INPUTS = tuple(dict.fromkeys((
    *SPARSE, *SLOW, "tests/o2a_print.sail", "tests/o2a_slow_print.sail",
    *(name for pair in SUITES.values() for name in pair[:2]),
    "tests/o2a_compare.py", "tests/o2a_compare_extra.py",
    "tests/o2a_mutations.py", "tests/o2a_scale.sail", "tests/print.splice",
    "scripts/check_o2a.py", "scripts/check.py", "upstreams.json",
)))
ACCEPTED_SHA = {
    "spec/o2a_sparse_map.sail":
        "6b93e35945c53297e606d2fae89f12954a3e56e36e78faa80b5d8ee99874747b",
    "spec/o2a_sparse_runner.sail":
        "98315039eb8a6dc937e095b5ada0003c219de61146677788f08c5ed223031e94",
    "tests/o2a_slow_control.sail":
        "7ed586822ba43c526fd0f012bd94f30306262aa23344e46ba9dc5d46e2e8e06d",
}
LABELS = (
    "ONE_KNOWN", "CHAIN", "CHAIN_REVERSED", "DEFAULT", "LATE_SET",
    "EAGER_ZERO", "FIXED_CONFLICT", "REPEATED", "POINTER_ALIAS",
    "ADDRESS_PRIORITY", "PUBLIC_PRIORITY", "TERMINAL_FRAME",
)
MUTANT_ASSERTIONS = {
    "pair_activation": "ONE_KNOWN",
    "output_activation": "LATE_SET",
    "eager_activation": "EAGER_ZERO",
}
SCALE_OUTPUT = b"SCALE_1000_OK\nSCALE_4000_OK\n"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_build(path: Path) -> Path:
    build = path.resolve()
    base = (ROOT / "build").resolve()
    require(base == ROOT / "build" and build.is_relative_to(base)
            and build != base,
            "O2a build must be a child of repository build/")
    return build


def logged(args, *, cwd: Path, env: dict[str, str], log: Path,
           timeout: int = 600) -> None:
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("wb") as stream:
        result = subprocess.run([str(arg) for arg in args], cwd=cwd, env=env,
                                stdout=stream, stderr=subprocess.STDOUT,
                                timeout=timeout)
    if result.returncode != 0:
        tail = log.read_bytes()[-4000:].decode(errors="replace")
        raise RuntimeError(f"command failed ({result.returncode}): {args}\n{tail}")


def execute(binary: Path, *, cwd: Path, env: dict[str, str], out: Path,
            err: Path, timeout: int = 600) -> None:
    with out.open("wb") as stdout, err.open("wb") as stderr:
        result = subprocess.run([str(binary)], cwd=cwd, env=env,
                                stdout=stdout, stderr=stderr, timeout=timeout)
    require(result.returncode == 0,
            f"{binary.name}: exit {result.returncode}: {err.read_text(errors='replace')}")
    require(err.read_bytes() == b"", f"{binary.name}: unexpected stderr")


def compile_c(*, sail_root: Path, files: list[Path], build: Path,
              env: dict[str, str], label: str) -> Path:
    sail = [sail_root / "sail", "--no-color", "--memo-z3-path",
            build / "smt-cache"]
    logged([*sail, "--just-check", *files], cwd=ROOT, env=env,
           log=build / f"{label}-typecheck.log")
    generated = build / label
    logged([*sail, "-c", "-O", *files, "-o", generated], cwd=ROOT, env=env,
           log=build / f"{label}-sail-c.log")
    runtime = sail_root / "lib"
    binary = build / f"{label}-c"
    logged(["cc", "-O2", "-I", runtime, generated.with_suffix(".c"),
            *[runtime / f"{name}.c" for name in
              ("sail", "rts", "elf", "sail_failure")],
            "-lgmp", "-o", binary], cwd=ROOT, env=env,
           log=build / f"{label}-cc.log")
    return binary


def compile_lean(*, sail_root: Path, support: Path, files: list[Path],
                 build: Path, env: dict[str, str], label: str) -> tuple[Path, Path]:
    staging = build / f"{label}-lean-staging"
    if staging.exists():
        shutil.rmtree(staging)
    staging.mkdir()
    sail = [sail_root / "sail", "--no-color", "--memo-z3-path",
            build / "smt-cache"]
    logged([*sail, "--splice", ROOT / "tests/print.splice", *files,
            "--lean", "--lean-single-file", "--lean-executable",
            "--lean-lib-path", support, "--lean-output-dir", staging,
            "-o", label], cwd=ROOT, env=env,
           log=build / f"{label}-sail-lean.log")
    project = staging / label
    require((project / "lean-toolchain").read_text().strip()
            == env["ELAN_TOOLCHAIN"], f"{label}: Lean toolchain differs from pin")
    logged(["lake", "update"], cwd=project, env=env,
           log=build / f"{label}-lake-update.log")
    logged(["lake", "build", "run"], cwd=project, env=env,
           log=build / f"{label}-lake-build.log")
    return project / ".lake/build/bin/run", project / f"{label.capitalize()}.lean"


def oracle(args: list[Path], *, env: dict[str, str], log: Path,
           expected: str) -> None:
    result = subprocess.run([sys.executable, "-O", *map(str, args)],
                            cwd=ROOT, env=env, capture_output=True,
                            timeout=120)
    log.write_bytes(result.stdout + result.stderr)
    require(result.returncode == 0 and result.stderr == b""
            and expected.encode() in result.stdout,
            f"oracle failed: {log.read_text(errors='replace')}")


def run_suite(name: str, *, sail_root: Path, support: Path, build: Path,
              env: dict[str, str]) -> dict:
    sparse_case, slow_case, count = SUITES[name]
    work = build / name
    work.mkdir(parents=True, exist_ok=True)
    sparse_files = [ROOT / item for item in
                    (*SPARSE, "tests/o2a_print.sail", sparse_case)]
    slow_files = [ROOT / item for item in
                  (*SLOW, "tests/o2a_slow_print.sail", slow_case)]
    c_binary = compile_c(sail_root=sail_root, files=sparse_files,
                         build=work, env=env, label="sparse")
    lean_binary, lean_source = compile_lean(
        sail_root=sail_root, support=support, files=sparse_files,
        build=work, env=env, label="sparse")
    slow_binary = compile_c(sail_root=sail_root, files=slow_files,
                            build=work, env=env, label="slow")
    outputs = {}
    for label, binary in (("c", c_binary), ("lean", lean_binary),
                          ("slow", slow_binary)):
        out, err = work / f"{label}.out", work / f"{label}.err"
        execute(binary, cwd=work, env=env, out=out, err=err)
        outputs[label] = out
    data = outputs["c"].read_bytes()
    require(data == outputs["lean"].read_bytes() == outputs["slow"].read_bytes(),
            f"{name}: sparse C/Lean and fresh slow C complete envelopes differ")
    require(data.count(b"BEGIN_O2a_ENVELOPE\n") == count,
            f"{name}: expected {count} complete envelopes")
    if name == "directed":
        oracle([ROOT / "tests/o2a_compare.py", outputs["c"], outputs["lean"]],
               env=env, log=work / "oracle.log",
               expected="12 complete envelopes parsed; C/Lean bytes equal")
    else:
        oracle([ROOT / "tests/o2a_compare_extra.py", outputs["c"],
                outputs["lean"], outputs["slow"]], env=env,
               log=work / "oracle.log",
               expected="14 complete extra envelopes parsed; C/Lean/slow bytes equal")
    return {
        "cases": count, "full_envelope_bytes_identical": True,
        "c_output_sha256": sha(outputs["c"]),
        "lean_output_sha256": sha(outputs["lean"]),
        "slow_output_sha256": sha(outputs["slow"]),
        "generated_c_sha256": sha(work / "sparse.c"),
        "generated_lean_sha256": sha(lean_source),
        "c_binary_sha256": sha(c_binary),
        "lean_binary_sha256": sha(lean_binary),
        "slow_binary_sha256": sha(slow_binary),
        "oracle_log_sha256": sha(work / "oracle.log"),
    }


def require_assertion_prefix(name: str, *, out: bytes, err: bytes,
                             returncode: int) -> dict:
    target = MUTANT_ASSERTIONS[name]
    require(returncode != 0 and err == f"Assertion failed: {target}\n".encode(),
            f"{name}: expected targeted {target} assertion, got {err!r}")
    prefix = LABELS[:LABELS.index(target)]
    cursor = 0
    end_marker = b"END_O2a_ENVELOPE\n"
    for label in prefix:
        marker = f"{label}\nBEGIN_O2a_ENVELOPE\n".encode()
        require(out.startswith(marker, cursor),
                f"{name}: incomplete preceding envelope {label}")
        end = out.find(end_marker, cursor + len(marker))
        require(end >= 0, f"{name}: missing end marker before {target}")
        cursor = end + len(end_marker)
    require(cursor == len(out), f"{name}: unexpected bytes after target {target}")
    return {"target_case": target, "completed_prefix_cases": len(prefix)}


def run_mutants(*, sail_root: Path, build: Path, env: dict[str, str],
                control: Path) -> list[dict]:
    mutations = runpy.run_path(str(ROOT / "tests/o2a_mutations.py"))
    mutants = build / "mutants"
    mutations["generate"](mutants)
    results = []
    for name in mutations["MUTATIONS"]:
        work = mutants / name
        work.mkdir(exist_ok=True)
        candidate = mutants / f"{name}.sail"
        files = [ROOT / item for item in
                 (*BASE, "spec/o2a_sparse_map.sail")]
        files += [candidate, ROOT / "tests/o2a_print.sail",
                  ROOT / "tests/o2a_cases.sail"]
        binary = compile_c(sail_root=sail_root, files=files,
                           build=work, env=env, label="mutant")
        out, err = work / "run.out", work / "run.err"
        with out.open("wb") as stdout, err.open("wb") as stderr:
            result = subprocess.run([str(binary)], cwd=work, env=env,
                                    stdout=stdout, stderr=stderr, timeout=120)
        data, error = out.read_bytes(), err.read_bytes()
        if name in MUTANT_ASSERTIONS:
            targeted = require_assertion_prefix(
                name, out=data, err=error, returncode=result.returncode)
        else:
            require(result.returncode == 0 and error == b""
                    and data.count(b"BEGIN_O2a_ENVELOPE\n") == 12,
                    "activation_order: mutant did not complete 12 envelopes")
            require(data != control.read_bytes(),
                    "activation_order: mutant envelopes unexpectedly equal control")
            check = subprocess.run(
                [sys.executable, "-O", str(ROOT / "tests/o2a_compare.py"),
                 str(out), str(out)], cwd=ROOT, env=env,
                capture_output=True, timeout=120)
            (work / "oracle.log").write_bytes(check.stdout + check.stderr)
            require(check.returncode != 0 and
                    b"chain propagation chronology" in check.stderr,
                    "activation_order: literal oracle did not catch CHAIN order")
            targeted = {"target_case": "CHAIN", "oracle_failure":
                        "chain propagation chronology"}
        results.append({
            "name": name, **targeted, "source_sha256": sha(candidate),
            "exit_code": result.returncode, "stdout_sha256": sha(out),
            "stderr_sha256": sha(err),
        })
    return results


def corruptions(*, build: Path, env: dict[str, str], control: Path) -> list[dict]:
    lines = control.read_text().splitlines()
    mutations = {}
    changed = lines.copy()
    pos = changed.index("CHECKER_REJECTED")
    require(changed[pos + 1:pos + 3] == ["BEGIN_O2a_ENVELOPE", "14"],
            "status corruption anchor moved")
    changed[pos + 2] = "1"
    mutations["status"] = (changed, "CHECKER_REJECTED: extra directed header")
    changed = lines.copy()
    pos = changed.index("DUPLICATE_ADVICE")
    require(changed[pos + 1:pos + 4] ==
            ["BEGIN_O2a_ENVELOPE", "1", "0"],
            "phase corruption anchor moved")
    changed[pos + 3] = "1"
    mutations["phase"] = (changed, "DUPLICATE_ADVICE: extra directed header")
    changed = lines.copy()
    pos = changed.index("DISJOINT_DEFAULT")
    end_cells = changed.index("END_CELLS", pos)
    require(changed[end_cells + 1:end_cells + 6]
            == ["3", "4", "6", "7", "END_PAIRS"],
            "pair corruption anchor moved")
    changed[end_cells + 1], changed[end_cells + 2] = (
        changed[end_cells + 2], changed[end_cells + 1])
    mutations["pair"] = (changed, "disjoint default status and original pair order")
    changed = lines.copy()
    pos = changed.index("DISJOINT_DEFAULT")
    event = changed.index("END_PAIRS", pos) + 1
    while changed[event] != "12":
        event += 14
        require(event < len(changed), "event corruption anchor missing")
    require(changed[event + 7] == "3", "event corruption index moved")
    changed[event + 7] = "8"
    mutations["event"] = (changed,
                          "terminal first-encounter default event order and origins")
    folder = build / "corruptions"
    folder.mkdir(exist_ok=True)
    results = []
    for name, (mutated, expected) in mutations.items():
        path = folder / f"{name}.out"
        path.write_text("\n".join(mutated) + "\n")
        check = subprocess.run(
            [sys.executable, "-O", str(ROOT / "tests/o2a_compare_extra.py"),
             str(path), str(path), str(path)], cwd=ROOT, env=env,
            capture_output=True, timeout=120)
        log = folder / f"{name}.log"
        log.write_bytes(check.stdout + check.stderr)
        require(check.returncode != 0 and expected.encode() in check.stderr,
                f"{name}: common-output corruption escaped literal oracle")
        results.append({"name": name, "exit_code": check.returncode,
                        "output_sha256": sha(path), "oracle_log_sha256": sha(log),
                        "detected": expected})
    return results


def early_pin_failure_probe(*, support: Path, build: Path,
                            env: dict[str, str]) -> dict:
    probe = build / "early-pin-probe"
    probe.mkdir(exist_ok=True)
    old_report = probe / "validation.json"
    old_report.write_text('{"stale_success": true}\n')
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts/check_o2a.py"),
         "--build", str(probe), "--sail-root", str(support)],
        cwd=ROOT, env=env, capture_output=True, timeout=120)
    log = probe / "forced-pin-failure.log"
    log.write_bytes(result.stdout + result.stderr)
    require(result.returncode != 0
            and b"sail revision differs from upstreams.json" in result.stderr
            and not old_report.exists(),
            "early pin failure retained a stale O2a success report")
    return {"forced_failure": "sail revision differs from upstreams.json",
            "old_success_removed": True, "log_sha256": sha(log)}


def scale(*, sail_root: Path, support: Path, build: Path,
          env: dict[str, str]) -> dict:
    work = build / "scale"
    work.mkdir(exist_ok=True)
    files = [ROOT / name for name in (*SPARSE, "tests/o2a_scale.sail")]
    c_binary = compile_c(sail_root=sail_root, files=files,
                         build=work, env=env, label="scale")
    lean_binary, _ = compile_lean(sail_root=sail_root, support=support,
                                  files=files, build=work, env=env,
                                  label="scale")
    measurements = {}
    for name, binary in (("c", c_binary), ("lean", lean_binary)):
        out, err, metrics = (work / f"{name}.out", work / f"{name}.err",
                             work / f"{name}.time")
        with out.open("wb") as stdout, err.open("wb") as stderr:
            result = subprocess.run(
                ["/usr/bin/time", "-f", "%e %M", "-o", str(metrics),
                 str(binary)], cwd=work, env=env, stdout=stdout,
                stderr=stderr, timeout=600)
        require(result.returncode == 0 and err.read_bytes() == b""
                and out.read_bytes() == SCALE_OUTPUT,
                f"scale {name}: marker, exit, or stderr mismatch")
        fields = metrics.read_text().split()
        require(len(fields) == 2, f"scale {name}: malformed time metrics")
        measurements[name] = {"wall_seconds": float(fields[0]),
                              "peak_rss_kb": int(fields[1]),
                              "output_sha256": sha(out)}
    require((work / "c.out").read_bytes() == (work / "lean.out").read_bytes(),
            "scale: C/Lean markers differ")
    return {"pair_insertions": 4000, "intermediate_check": 1000,
            "memory_cells": 65536, "scope": "bounded runner pair-insertion probe",
            "measurements": measurements}


def validate(*, sail_root: Path, support: Path, build: Path,
             env: dict[str, str]) -> dict:
    sail_root, support, build = sail_root.resolve(), support.resolve(), checked_build(build)
    build.mkdir(parents=True, exist_ok=True)
    (build / "validation.json").unlink(missing_ok=True)
    snapshots = {name: sha(ROOT / name) for name in INPUTS}
    for name, accepted in ACCEPTED_SHA.items():
        require(snapshots[name] == accepted, f"O2a accepted source changed: {name}")
    pin_failure_result = early_pin_failure_probe(support=support, build=build,
                                                 env=env)
    suites = {
        name: run_suite(name, sail_root=sail_root, support=support,
                        build=build, env=env)
        for name in SUITES
    }
    mutation_results = run_mutants(
        sail_root=sail_root, build=build, env=env,
        control=build / "directed/c.out")
    corruption_results = corruptions(
        build=build, env=env, control=build / "extra/c.out")
    scale_result = scale(sail_root=sail_root, support=support,
                         build=build, env=env)
    for name, digest in snapshots.items():
        require(sha(ROOT / name) == digest,
                f"O2a input changed during campaign: {name}")
    report = {
        "completed_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "equality-only bounded O2a runner; no full O2 or formal bridge",
        "backends": ["c", "lean"], "c_sail_options": ["-O"],
        "source_sha256": snapshots,
        "complete_envelope_cases": sum(item[2] for item in SUITES.values()),
        "suites": suites, "mutations": mutation_results,
        "common_output_corruptions": corruption_results,
        "early_pin_failure_probe": pin_failure_result,
        "scale": scale_result,
    }
    (build / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sail-root", type=Path, default=ROOT.parent / "sail")
    parser.add_argument("--lean-support", type=Path)
    parser.add_argument("--build", type=Path, default=ROOT / "build/o2a")
    args = parser.parse_args()
    build = checked_build(args.build)
    build.mkdir(parents=True, exist_ok=True)
    (build / "validation.json").unlink(missing_ok=True)
    sail_root = args.sail_root.resolve()
    support = (args.lean_support or sail_root / "_deps/lean-sail").resolve()
    pins = json.loads((ROOT / "upstreams.json").read_text())
    for name, path in (("sail", sail_root), ("lean_sail", support)):
        revision = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=path, text=True).strip()
        require(revision == pins[name]["revision"],
                f"{name} revision differs from upstreams.json")
        subprocess.run(["git", "diff", "--quiet", "HEAD"], cwd=path,
                       check=True)
    env = dict(os.environ)
    env["PATH"] = str(sail_root / "_deps/z3/bin") + os.pathsep + env["PATH"]
    env["ELAN_TOOLCHAIN"] = pins["lean_toolchain"]
    env["LEANVM_NUM_THREADS"] = "1"
    require(pins["sail"]["revision"] in subprocess.check_output(
        [str(sail_root / "sail"), "--version"], env=env, text=True),
        "Sail executable does not match its source revision")
    print(json.dumps(validate(sail_root=sail_root, support=support,
                              build=build, env=env), indent=2))


if __name__ == "__main__":
    main()
