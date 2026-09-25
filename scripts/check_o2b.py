#!/usr/bin/env python3
"""Validate bounded explicit O2b MUL candidates in optimized C and Lean."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import subprocess
import sys

import check_o2a

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tests"))
import o2b_compare  # noqa: E402
import o2b_corruptions  # noqa: E402

BASE = check_o2a.BASE
MODEL = BASE + ("spec/o2a_sparse_map.sail", "spec/o2a_sparse_runner.sail",
                "spec/o2b_candidate.sail")
PRINT = ("tests/o2a_print.sail", "tests/o2b_print.sail")
INPUTS = tuple(dict.fromkeys((
    *MODEL, *PRINT, "tests/o2a_slow_control.sail",
    "tests/o2b_cases.sail", "tests/o2b_checker_control.sail",
    "tests/o2b_parity_directed.sail", "tests/o2b_parity_extra.sail",
    "tests/o2b_compare.py", "tests/o2b_corruptions.py",
    "tests/o2b_mutations.py", "tests/o2b_oracle.py", "tests/print.splice",
    "scripts/check_o2a.py", "scripts/check_o2b.py", "scripts/check.py",
    "upstreams.json",
)))
PARITY = {
    "directed": ("tests/o2b_parity_directed.sail", 12,
                 "b0e72e8d0c12fb1dc997dd5ae88d9d24a470834201ed272faebf03082b4c7e45"),
    "extra": ("tests/o2b_parity_extra.sail", 14,
              "1ca81e0d22cdb63af4b714e6cefe316c3f3ce28ca51853a104d9ce31d775b97b"),
}


def require(ok: bool, why: str) -> None:
    if not ok:
        raise RuntimeError(why)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_build(path: Path) -> Path:
    build = path.resolve()
    base = (ROOT / "build").resolve()
    require(base == ROOT / "build" and build.is_relative_to(base) and
            build != base, "O2b build must be a child of repository build/")
    return build


def files(*names: str) -> list[Path]:
    return [ROOT / name for name in names]


def run_binary(binary: Path, work: Path, label: str,
               env: dict[str, str]) -> bytes:
    out, err = work / f"{label}.out", work / f"{label}.err"
    check_o2a.execute(binary, cwd=work, env=env, out=out, err=err)
    return out.read_bytes()


def python_oracle(command: list[str], work: Path, label: str,
                  env: dict[str, str], expected: str) -> str:
    result = subprocess.run([sys.executable, *command], cwd=ROOT, env=env,
                            capture_output=True, timeout=120)
    log = work / f"{label}.log"
    log.write_bytes(result.stdout + result.stderr)
    require(result.returncode == 0 and result.stderr == b"" and
            expected.encode() in result.stdout,
            f"{label}: Python oracle failed: {log.read_text(errors='replace')}")
    return sha(log)


def compile_pair(name: str, fixture: str, *, sail_root: Path, support: Path,
                 build: Path, env: dict[str, str]) -> tuple[bytes, dict]:
    work = build / name
    work.mkdir(parents=True, exist_ok=True)
    source = files(*MODEL, *PRINT, fixture)
    c_binary = check_o2a.compile_c(sail_root=sail_root, files=source,
                                    build=work, env=env, label=name)
    lean_binary, _ = check_o2a.compile_lean(
        sail_root=sail_root, support=support, files=source,
        build=work, env=env, label=name)
    lean_sources = list(lean_binary.parents[3].glob("*.lean"))
    require(len(lean_sources) == 1,
            f"{name}: expected one generated root Lean source")
    lean_source = lean_sources[0]
    c_data = run_binary(c_binary, work, "c", env)
    lean_data = run_binary(lean_binary, work, "lean", env)
    require(c_data == lean_data, f"{name}: C/Lean full envelopes differ")
    result = {
        "c_output_sha256": sha(work / "c.out"),
        "lean_output_sha256": sha(work / "lean.out"),
        "generated_c_sha256": sha(work / f"{name}.c"),
        "generated_lean_sha256": sha(lean_source),
        "c_binary_sha256": sha(c_binary),
        "lean_binary_sha256": sha(lean_binary),
    }
    return c_data, result


def directed(*, sail_root: Path, support: Path, build: Path,
             env: dict[str, str]) -> dict:
    data, evidence = compile_pair("directed", "tests/o2b_cases.sail",
                                  sail_root=sail_root, support=support,
                                  build=build, env=env)
    cases = o2b_compare.verify(data, data)
    work = build / "directed"
    normal = python_oracle([str(ROOT / "tests/o2b_compare.py"),
                            str(work / "c.out"), str(work / "lean.out")],
                           work, "oracle", env,
                           "47 complete O2b envelopes parsed; C/Lean bytes equal")
    optimized = python_oracle(["-O", str(ROOT / "tests/o2b_compare.py"),
                               str(work / "c.out"), str(work / "lean.out")],
                              work, "oracle-optimized", env,
                              "47 complete O2b envelopes parsed; C/Lean bytes equal")
    controls = {}
    for mode, flags in (("normal", []), ("optimized", ["-O"])):
        log_sha = python_oracle([*flags, str(ROOT / "tests/o2b_corruptions.py"),
                                 str(work / "c.out"),
                                 str(work / f"corruptions-{mode}")],
                                work, f"corruptions-{mode}", env,
                                "14 identical C/Lean corruptions rejected")
        controls[mode] = {"count": 14, "log_sha256": log_sha}
    return {**evidence, "cases": len(cases),
            "normal_oracle_log_sha256": normal,
            "optimized_oracle_log_sha256": optimized,
            "common_output_corruptions": controls}


def checker_control(*, sail_root: Path, support: Path, build: Path,
                    env: dict[str, str]) -> dict:
    data, evidence = compile_pair("checker", "tests/o2b_checker_control.sail",
                                  sail_root=sail_root, support=support,
                                  build=build, env=env)
    case = o2b_compare.verify_checker_control(data, data)
    work = build / "checker"
    code = ("import sys; sys.path.insert(0, 'tests'); "
            "from pathlib import Path; from o2b_compare import verify_checker_control; "
            "a=Path(sys.argv[1]).read_bytes(); b=Path(sys.argv[2]).read_bytes(); "
            "verify_checker_control(a,b); print('synthetic checker control passed')")
    optimized = python_oracle(["-O", "-c", code,
                               str(work / "c.out"), str(work / "lean.out")],
                              work, "oracle-optimized", env,
                              "synthetic checker control passed")
    return {**evidence, "case": case["name"],
            "scope": "synthetic direct step-to-completion wrong-verdict control",
            "optimized_oracle_log_sha256": optimized}


def parity(*, sail_root: Path, support: Path, build: Path,
           env: dict[str, str]) -> dict:
    results = {}
    for name, (fixture, count, accepted_hash) in PARITY.items():
        data, evidence = compile_pair(f"parity_{name}", fixture,
                                      sail_root=sail_root, support=support,
                                      build=build, env=env)
        require(data.count(b"BEGIN_O2a_ENVELOPE\n") == count and
                hashlib.sha256(data).hexdigest() == accepted_hash,
                f"{name}: complete accepted O2a envelopes changed")
        results[name] = {**evidence, "envelopes": count,
                         "runner_calls_with_empty_and_inactive_plans":
                         count if name == "directed" else count - 2,
                         "accepted_output_sha256": accepted_hash}
    return results


def mutant_detector(data: bytes, error: bytes, code: int, target: str,
                    labels: list[str]) -> str:
    position = labels.index(target)
    if code != 0:
        require(error == f"Assertion failed: {target}\n".encode(),
                f"mutant: wrong failure before {target}: {error!r}")
        prefix = o2b_compare.parse(data) if data else []
        require([case["name"] for case in prefix] == labels[:position],
                f"mutant: incomplete or wrong prefix before {target}")
        return "targeted Sail assertion"
    require(error == b"", f"mutant: unexpected stderr at {target}")
    parsed = o2b_compare.parse(data)
    require([case["name"] for case in parsed] == labels,
            f"mutant: did not complete 47 envelopes at {target}")
    try:
        o2b_compare.verify(data, data)
    except RuntimeError as failure:
        require(target in str(failure),
                f"mutant: wrong literal-oracle rejection at {target}: {failure}")
        return f"literal oracle: {failure}"
    raise RuntimeError(f"mutant: {target} escaped assertion and literal oracle")


def mutants(*, sail_root: Path, build: Path, env: dict[str, str]) -> list[dict]:
    module = runpy.run_path(str(ROOT / "tests/o2b_mutations.py"))
    work = build / "mutants"
    module["generate"](work)
    labels = re.findall(r'b_ok\("([A-Z0-9_]+)"',
                        (ROOT / "tests/o2b_cases.sail").read_text())
    require(len(labels) == 47 and len(set(labels)) == 47,
            "mutant: directed source label inventory changed")
    results = []
    for name, (_, _, target) in module["MUTATIONS"].items():
        candidate = work / f"{name}.sail"
        trial = work / name
        trial.mkdir(exist_ok=True)
        source = files(*BASE, "spec/o2a_sparse_map.sail",
                       "spec/o2a_sparse_runner.sail")
        source += [candidate, *files(*PRINT, "tests/o2b_cases.sail")]
        binary = check_o2a.compile_c(sail_root=sail_root, files=source,
                                      build=trial, env=env, label="mutant")
        out, err = trial / "run.out", trial / "run.err"
        with out.open("wb") as stdout, err.open("wb") as stderr:
            run = subprocess.run([str(binary)], cwd=trial, env=env,
                                 stdout=stdout, stderr=stderr, timeout=120)
        detector = mutant_detector(out.read_bytes(), err.read_bytes(),
                                   run.returncode, target, labels)
        results.append({"name": name, "target": target, "detector": detector,
                        "exit_code": run.returncode,
                        "source_sha256": sha(candidate),
                        "stdout_sha256": sha(out), "stderr_sha256": sha(err),
                        "generated_c_sha256": sha(trial / "mutant.c"),
                        "binary_sha256": sha(binary)})
    return results


def early_pin_failure_probe(*, support: Path, build: Path,
                            env: dict[str, str]) -> dict:
    probe = build / "early-pin-probe"
    probe.mkdir(exist_ok=True)
    old = probe / "validation.json"
    old.write_text('{"stale_success": true}\n')
    result = subprocess.run([sys.executable, str(ROOT / "scripts/check_o2b.py"),
                             "--build", str(probe), "--sail-root", str(support)],
                            cwd=ROOT, env=env, capture_output=True, timeout=120)
    log = probe / "forced-pin-failure.log"
    log.write_bytes(result.stdout + result.stderr)
    require(result.returncode != 0 and
            b"sail revision differs from upstreams.json" in result.stderr and
            not old.exists(), "early pin failure retained stale O2b success")
    return {"old_success_removed": True, "log_sha256": sha(log)}


def validate(*, sail_root: Path, support: Path, build: Path,
             env: dict[str, str]) -> dict:
    sail_root, support, build = (sail_root.resolve(), support.resolve(),
                                 checked_build(build))
    build.mkdir(parents=True, exist_ok=True)
    (build / "validation.json").unlink(missing_ok=True)
    snapshot = {name: sha(ROOT / name) for name in INPUTS}
    for name, accepted in check_o2a.ACCEPTED_SHA.items():
        require(snapshot[name] == accepted,
                f"accepted O2a seam/source changed: {name}")
    pin_probe = early_pin_failure_probe(support=support, build=build, env=env)
    directed_result = directed(sail_root=sail_root, support=support,
                               build=build, env=env)
    checker_result = checker_control(sail_root=sail_root, support=support,
                                     build=build, env=env)
    parity_result = parity(sail_root=sail_root, support=support,
                           build=build, env=env)
    mutant_results = mutants(sail_root=sail_root, build=build, env=env)
    for name, digest in snapshot.items():
        require(sha(ROOT / name) == digest,
                f"O2b input changed during campaign: {name}")
    report = {
        "completed_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "bounded explicit MUL candidates; no inverse generation or ISA proof",
        "backends": ["c", "lean"], "c_sail_options": ["-O"],
        "source_sha256": snapshot,
        "directed": directed_result, "checker_control": checker_result,
        "o2a_full_result_parity": parity_result,
        "source_mutants": mutant_results,
        "early_pin_failure_probe": pin_probe,
    }
    (build / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sail-root", type=Path, default=ROOT.parent / "sail")
    parser.add_argument("--lean-support", type=Path)
    parser.add_argument("--build", type=Path, default=ROOT / "build/o2b")
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
        subprocess.run(["git", "diff", "--quiet", "HEAD"], cwd=path, check=True)
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
