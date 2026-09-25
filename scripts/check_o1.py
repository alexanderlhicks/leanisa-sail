#!/usr/bin/env python3
"""Run the O1 full-envelope C/Lean and mutation gate in an isolated build tree."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[1]
SAIL_FILES = (
    "spec/field.sail", "spec/blake2s.sail", "spec/machine.sail",
    "spec/forward.sail", "tests/o1_print.sail", "tests/o1_cases.sail",
)
INPUTS = SAIL_FILES + (
    "tests/o1_compare.py", "tests/o1_mutations.py", "tests/print.splice",
    "scripts/check_o1.py", "upstreams.json",
)
MUTANT_FAILURES = {
    "eager_default": ("XOR_CANCELLATION_EARLY_DEFAULT", "XOR early default retained"),
    "deferred_pair": ("DEREF_CELL_ONE_UNKNOWN", "one Cell endpoint defaulted"),
    "shape_priority": ("INVALID_SHAPE_PRIORITY", "shape before public/advice/fuel"),
    "fuel_order": ("SET", "SET"),
    "failure_priority": ("DEREF_TARGET_ACCESS_PRIORITY", "DEREF_TARGET_ACCESS_PRIORITY"),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args, *, cwd: Path, env: dict[str, str], stdout: Path | None = None,
            stderr: Path | None = None, timeout: int = 600) -> None:
    argv = [str(arg) for arg in args]
    if stdout is None:
        subprocess.run(argv, cwd=cwd, env=env, check=True, timeout=timeout)
    else:
        require(stderr is not None, "logged command requires stderr path")
        with stdout.open("wb") as out, stderr.open("wb") as err:
            subprocess.run(argv, cwd=cwd, env=env, stdout=out, stderr=err,
                           check=True, timeout=timeout)


def comparator_module():
    path = ROOT / "tests/o1_compare.py"
    spec = importlib.util.spec_from_file_location("leanisa_o1_compare", path)
    require(spec is not None and spec.loader is not None,
            "cannot load O1 full-envelope comparator")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def require_mutant_failure(*, name: str, output: bytes, error: bytes,
                           returncode: int, case_labels: list[str]) -> dict:
    target, assertion = MUTANT_FAILURES[name]
    require(target in case_labels, f"{name}: missing targeted case {target}")
    require(returncode != 0, f"{name}: mutant completed successfully")
    require(error == f"Assertion failed: {assertion}\n".encode(),
            f"{name}: expected targeted assertion {assertion!r}, got {error!r}")
    previous = case_labels[:case_labels.index(target)]
    cursor = 0
    end_marker = b"END_O1_ENVELOPE\n"
    for label in previous:
        marker = f"{label}\nBEGIN_O1_ENVELOPE\n".encode()
        require(output.startswith(marker, cursor),
                f"{name}: expected complete preceding case {label}")
        end = output.find(end_marker, cursor + len(marker))
        require(end >= 0, f"{name}: preceding case {label} lacks envelope end")
        cursor = end + len(end_marker)
    require(cursor == len(output),
            f"{name}: output extends past target case {target}")
    return {"target_case": target, "target_assertion": assertion,
            "completed_prefix_cases": len(previous)}


def validate(*, sail_root: Path, support: Path, build: Path,
             env: dict[str, str]) -> dict:
    """Fail closed; publish validation.json only after every control passes."""
    sail_root, support, build = sail_root.resolve(), support.resolve(), build.resolve()
    require(build.is_relative_to(ROOT / "build"),
            "O1 build must stay below repository build/")
    build.mkdir(parents=True, exist_ok=True)
    (build / "validation.json").unlink(missing_ok=True)
    snapshots = {name: sha(ROOT / name) for name in INPUTS}
    sail = [sail_root / "sail", "--no-color", "--memo-z3-path",
            build / "smt-cache"]
    files = [ROOT / name for name in SAIL_FILES]
    command(sail + ["--just-check", *files], cwd=ROOT, env=env)
    c_path = build / "o1-c"
    command(sail + ["-c", "-O", *files, "-o", build / "o1"],
            cwd=ROOT, env=env)
    runtime = sail_root / "lib"
    command(["cc", "-O2", "-I", runtime, build / "o1.c",
             *[runtime / f"{name}.c" for name in
               ("sail", "rts", "elf", "sail_failure")],
             "-lgmp", "-o", c_path], cwd=ROOT, env=env)
    staging = build / "lean-staging"
    if staging.exists():
        shutil.rmtree(staging)
    staging.mkdir()
    command(sail + ["--splice", ROOT / "tests/print.splice", *files,
                    "--lean", "--lean-single-file", "--lean-executable",
                    "--lean-lib-path", support, "--lean-output-dir", staging,
                    "-o", "o1"], cwd=ROOT, env=env)
    project = staging / "o1"
    require((project / "lean-toolchain").read_text().strip()
            == env.get("ELAN_TOOLCHAIN"), "O1 Lean toolchain differs from pin")
    command(["lake", "update"], cwd=project, env=env)
    command(["lake", "build", "run"], cwd=project, env=env)
    lean_path = project / ".lake/build/bin/run"
    outputs = build / "outputs"
    outputs.mkdir(exist_ok=True)
    c_output, lean_output = outputs / "c.out", outputs / "lean.out"
    for binary, destination in ((c_path, c_output), (lean_path, lean_output)):
        with destination.open("wb") as out:
            subprocess.run([str(binary)], cwd=build, env=env, stdout=out,
                           check=True, timeout=600)
    require(c_output.read_bytes() == lean_output.read_bytes(),
            "O1 C and Lean full envelopes differ")
    comparator = comparator_module()
    require(comparator.parse(c_output) == comparator.parse(lean_output),
            "O1 parsed C and Lean envelopes differ")
    require(c_output.read_bytes().count(b"BEGIN_O1_ENVELOPE\n") == 49,
            "O1 case count differs from accepted directed set")
    mutants_dir = build / "mutants"
    command(["python3", ROOT / "tests/o1_mutations.py", "--out", mutants_dir],
            cwd=ROOT, env=env)
    mutation_results = []
    case_labels = [label for label, _, _ in comparator.EXPECTED]
    require(len(case_labels) == 49 and len(set(case_labels)) == 49,
            "O1 directed case list is not exactly 49 unique labels")
    for name in MUTANT_FAILURES:
        candidate = mutants_dir / name
        work = candidate / "build"
        work.mkdir(exist_ok=True)
        for test in ("o1_print.sail", "o1_cases.sail", "o1_compare.py"):
            require(sha(candidate / "tests" / test) == sha(ROOT / "tests" / test),
                    f"{name}: mutation control changed")
        mutant_files = [candidate / relative for relative in SAIL_FILES]
        command([sail_root / "sail", "--no-color", "--memo-z3-path",
                 work / "smt-cache", "-c", "-O", *mutant_files,
                 "-o", work / "o1-mutant"], cwd=work, env=env)
        binary = work / "o1-mutant"
        command(["cc", "-O2", "-I", runtime, binary.with_suffix(".c"),
                 *[runtime / f"{part}.c" for part in
                   ("sail", "rts", "elf", "sail_failure")],
                 "-lgmp", "-o", binary], cwd=work, env=env)
        stdout, stderr = work / "run.stdout", work / "run.stderr"
        with stdout.open("wb") as out, stderr.open("wb") as err:
            result = subprocess.run([str(binary)], cwd=work, env=env,
                                    stdout=out, stderr=err, timeout=120)
        targeted = require_mutant_failure(
            name=name, output=stdout.read_bytes(), error=stderr.read_bytes(),
            returncode=result.returncode, case_labels=case_labels)
        mutation_results.append({
            "name": name, **targeted,
            "source_sha256": sha(candidate / "spec/forward.sail"),
            "exit_code": result.returncode,
            "stdout_sha256": sha(stdout), "stderr_sha256": sha(stderr),
        })
    for name, digest in snapshots.items():
        require(sha(ROOT / name) == digest, f"O1 input changed during campaign: {name}")
    report = {
        "completed_utc": datetime.now(timezone.utc).isoformat(),
        "cases": 49, "backends": ["c", "lean"],
        "c_sail_options": ["-O"],
        "source_sha256": snapshots,
        "c_output_sha256": sha(c_output),
        "lean_output_sha256": sha(lean_output),
        "generated_c_sha256": sha(build / "o1.c"),
        "generated_lean_sha256": sha(project / "O1.lean"),
        "c_binary_sha256": sha(c_path),
        "lean_binary_sha256": sha(lean_path),
        "full_envelope_bytes_identical": True,
        "mutations": mutation_results,
    }
    (build / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sail-root", type=Path, default=ROOT.parent / "sail")
    parser.add_argument("--lean-support", type=Path)
    args = parser.parse_args()
    sail_root = args.sail_root.resolve()
    support = (args.lean_support or sail_root / "_deps/lean-sail").resolve()
    pins = json.loads((ROOT / "upstreams.json").read_text())
    for name, path in (("sail", sail_root), ("lean_sail", support)):
        revision = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=path, text=True
        ).strip()
        require(revision == pins[name]["revision"],
                f"{name} revision differs from upstreams.json")
        subprocess.run(["git", "diff", "--quiet", "HEAD"], cwd=path,
                       check=True)
    env = dict(os.environ)
    env["PATH"] = str(sail_root / "_deps/z3/bin") + os.pathsep + env["PATH"]
    env["ELAN_TOOLCHAIN"] = pins["lean_toolchain"]
    require(pins["sail"]["revision"] in subprocess.check_output(
        [str(sail_root / "sail"), "--version"], env=env, text=True),
        "Sail executable does not match its source revision")
    print(json.dumps(validate(sail_root=sail_root, support=support,
                              build=ROOT / "build/o1", env=env), indent=2))


if __name__ == "__main__":
    main()
