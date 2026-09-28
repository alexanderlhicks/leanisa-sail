#!/usr/bin/env python3
"""Build the leanerVM JSON oracle with isolated outputs and pinned source dependencies.

The evaluator uses Lean's interpreter to avoid eager native initialization of the pinned
BF64 Fintype instance. CompPoly and leanerVM modules are rebuilt from source. Prepared
Mathlib dependency caches are read only; no command writes to an implementation checkout.
Set LEANERVM_DEPENDENCIES_DIR to an existing pinned Lake package directory to reuse caches.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import time
import tempfile

LEANERVM_REVISION = "97ac443ae91d106333c1482b7164dc12c174bbe1"
COMPPOLY_REVISION = "3468b38c8fd270f93f55a259220a8abc544e7437"
MATHLIB_REVISION = "0df444a360eaa60ab8c11dca51a86af692955474"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
LEAN_GITHASH = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
IMPORT = re.compile(r"^(?:(?:public|meta) )?import (\S+)", re.MULTILINE)


def _clean_env() -> dict:
    return {key: value for key, value in os.environ.items()
            if not key.startswith(("GIT_", "LEAN_", "LAKE_"))}


def _git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", "--no-replace-objects", "-C", str(root), *args], text=True,
                                   env=_clean_env()).strip()


def _pin(root: Path, revision: str, label: str) -> str:
    actual = _git(root, "rev-parse", "HEAD")
    expected = _git(root, "rev-parse", f"{revision}^{{commit}}")
    if actual != expected:
        raise RuntimeError(f"{label} checkout revision differs from the supported pin")
    if _git(root, "status", "--porcelain", "--untracked-files=all"):
        raise RuntimeError(f"{label} checkout is dirty")
    # Git status alone can hide assume-unchanged/skip-worktree paths. Bind each tracked
    # working-tree byte sequence to its pinned blob, including symlink contents.
    entries = subprocess.check_output(["git", "--no-replace-objects", "-C", str(root), "ls-tree", "-rz", "HEAD"],
                                      env=_clean_env())
    for entry in entries.split(b"\0"):
        if not entry:
            continue
        metadata, name = entry.split(b"\t", 1)
        mode, kind, digest = metadata.split()
        path = root / os.fsdecode(name)
        if kind != b"blob":
            raise RuntimeError(f"{label} has an unsupported Git tree entry")
        if path.is_symlink():
            if mode != b"120000" or path.suffix == ".lean" or path.name == "lean-toolchain":
                raise RuntimeError(f"{label} source symlinks are unsupported")
            contents = os.fsencode(os.readlink(path))
        else:
            contents = path.read_bytes()
        blob = b"blob " + str(len(contents)).encode() + b"\0" + contents
        if hashlib.sha1(blob).hexdigest().encode() != digest:
            raise RuntimeError(f"{label} source bytes differ from the supported pin: {os.fsdecode(name)}")
    return actual


def _memory_limit() -> None:
    resource.setrlimit(resource.RLIMIT_AS, (32 << 30, 32 << 30))


def build(root: Path, leanervm: Path, build: Path, timeout: float) -> dict:
    """Return command and provenance after rebuilding the required source import cone.

    ``leanervm`` must be a clean pinned checkout with CompPoly under .lake/packages.
    The Mathlib cache directory may be supplied separately. All generated files and build
    diagnostics stay under ``build/lean``. A build deadline and 32 GiB virtual-memory limit fail
    explicitly; resource failures are never interpreted as semantic rejections.
    """
    deadline = time.monotonic() + timeout
    root, leanervm, build = root.resolve(), leanervm.resolve(), build.resolve()
    source = root / "tests/differential/LeanerVMOracle.lean"
    if source.resolve() != source.absolute():
        raise RuntimeError("adapter source symlinks are unsupported")
    adapter_bytes = source.read_bytes()
    adapter_hash = hashlib.sha256(adapter_bytes).hexdigest()
    revision = _pin(leanervm, LEANERVM_REVISION, "leanerVM")
    if (leanervm / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise RuntimeError("leanerVM toolchain differs from the supported pin")
    cp = leanervm / ".lake/packages/CompPoly"
    cp_revision = _pin(cp, COMPPOLY_REVISION, "CompPoly")
    deps = Path(os.environ.get("LEANERVM_DEPENDENCIES_DIR", leanervm / ".lake/packages"))
    mathlib = deps / "mathlib"
    _pin(mathlib, MATHLIB_REVISION, "Mathlib")
    elan = shutil.which("elan")
    if not elan:
        raise RuntimeError("elan is required to select the pinned Lean toolchain")
    actual_compiler = subprocess.check_output([elan, "run", TOOLCHAIN, "lean", "--githash"],
                                               text=True, env=_clean_env()).strip()
    if actual_compiler != LEAN_GITHASH:
        raise RuntimeError("Lean compiler commit differs from the supported toolchain")
    output = build / "lean"
    output.mkdir(parents=True, exist_ok=True)
    library = Path(tempfile.mkdtemp(prefix="lib-", dir=output))
    # The required source modules always precede dependency caches in LEAN_PATH.
    # No prebuilt CompPoly or leanerVM module is accepted here.
    dependency_revisions = {"CompPoly": cp_revision, "mathlib": MATHLIB_REVISION}
    cache_owners = [mathlib]
    manifest = json.loads((mathlib / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        package_root = deps / package["name"]
        dependency_revisions[package["name"]] = _pin(package_root, package["rev"], package["name"])
        if (package_root / ".lake/build/lib/lean").is_dir():
            cache_owners.append(package_root)
    caches = [p / ".lake/build/lib/lean" for p in cache_owners]
    # Cache binaries are a declared trust boundary: bind the exact artifacts read to
    # the campaign provenance, with their owning source revisions checked above.
    cache_hashes = {}
    for owner, cache in zip(cache_owners, caches):
        digest = hashlib.sha256()
        count = 0
        for artifact in sorted(cache.rglob("*")):
            if time.monotonic() >= deadline:
                raise RuntimeError("leanerVM dependency verification deadline exceeded")
            if not artifact.is_file() or artifact.suffix not in {".olean", ".private", ".ir", ".sig"}:
                continue
            if artifact.is_symlink():
                raise RuntimeError("dependency cache symlinks are unsupported")
            file_hash = hashlib.sha256()
            with artifact.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1 << 20), b""):
                    file_hash.update(chunk)
            digest.update(str(artifact.relative_to(cache)).encode() + b"\0" + file_hash.digest())
            count += 1
        cache_hashes[owner.name] = {"sha256": digest.hexdigest(), "artifacts": count}
    if not (mathlib / ".lake/build/lib/lean/Mathlib").is_dir():
        raise RuntimeError("prepare the pinned Mathlib cache before building the oracle")
    env = dict(_clean_env(), LEAN_PATH=os.pathsep.join(map(str, [library, *caches])))
    source_hashes = {}
    visited = set()

    def compile_module(module: str) -> None:
        if module in visited:
            return
        visited.add(module)
        owner = cp if module.startswith("CompPoly.") else leanervm
        relative = Path(module.replace(".", "/")).with_suffix(".lean")
        source = owner / relative
        if source.resolve() != source.absolute():
            raise RuntimeError("compiled source symlinks are unsupported")
        text = source.read_text()
        source_hashes[f"{'CompPoly' if owner == cp else 'leanerVM'}/{relative}"] = (
            hashlib.sha256(source.read_bytes()).hexdigest())
        for imported in IMPORT.findall(text):
            if imported.startswith(("CompPoly.", "LeanerVM.")):
                compile_module(imported)
        target = library / relative.with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise RuntimeError("leanerVM oracle build deadline exceeded")
        command = [elan, "run", TOOLCHAIN, "lean", "-j1", "-DwarningAsError=true",
                   "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                   "-o", str(target), "-i", str(target.with_suffix(".ilean")), str(relative)]
        with (output / "build.stdout").open("a") as stdout, (
                output / "build.stderr").open("a") as stderr:
            try:
                result = subprocess.run(command, cwd=owner, env=env, stdout=stdout,
                                        stderr=stderr, timeout=remaining, preexec_fn=_memory_limit)
            except subprocess.TimeoutExpired as exc:
                raise RuntimeError(f"leanerVM module build timed out: {module}") from exc
        if result.returncode:
            raise RuntimeError(f"leanerVM module build failed ({result.returncode}): {module}; "
                               f"diagnostics in {output}")

    for module in ["LeanerVM.Semantics.Checker", "LeanerVM.Arithmetization.Bytecode"]:
        compile_module(module)
    oracle = output / "LeanerVMOracle.lean"
    oracle.write_bytes(adapter_bytes)
    source_hashes["adapter/LeanerVMOracle.lean"] = adapter_hash
    # Check adapter elaboration before starting the campaign. --run then evaluates main
    # with lazy imported IR, without linking native eager field initializers.
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise RuntimeError("leanerVM oracle build deadline exceeded")
    check = [elan, "run", TOOLCHAIN, "lean", "-j1", "-DwarningAsError=true", str(oracle)]
    result = subprocess.run(check, env=env, capture_output=True, text=True,
                            timeout=remaining, preexec_fn=_memory_limit)
    (output / "adapter.stdout").write_text(result.stdout)
    (output / "adapter.stderr").write_text(result.stderr)
    if result.returncode:
        raise RuntimeError(f"leanerVM adapter failed ({result.returncode}); diagnostics in {output}")
    command = ["env", "-u", "LEAN_SYSROOT", "-u", "LEAN_SRC_PATH", f"LEAN_PATH={env['LEAN_PATH']}", elan, "run", TOOLCHAIN, "lean", "-j1",
               "-DwarningAsError=true", "--run", str(oracle)]
    # Recheck after compilation so a concurrent edit cannot leave a misleading source map.
    _pin(leanervm, LEANERVM_REVISION, "leanerVM")
    _pin(cp, COMPPOLY_REVISION, "CompPoly")
    for owner in cache_owners:
        _pin(owner, dependency_revisions[owner.name], owner.name)
    if source.read_bytes() != adapter_bytes or oracle.read_bytes() != adapter_bytes:
        raise RuntimeError("adapter source changed while building")
    provenance = {"command": command, "revision": revision, "mode": "lean-interpreter",
                  "dependency_revisions": dependency_revisions, "dependency_cache_hashes": cache_hashes,
                  "source_hashes": source_hashes, "toolchain": TOOLCHAIN, "compiler_commit": actual_compiler,
                  "dependency_patch": None, "compiler_virtual_memory_limit_gib": 32}
    (output / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    return provenance
