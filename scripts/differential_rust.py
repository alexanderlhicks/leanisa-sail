"""Build the differential adapter against the frozen Rust leanVM source."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess

REVISION = "48a904208d682848dac0e18ef8b01ebfc40df9ad"


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _regular_bytes(path: Path, label: str) -> bytes:
    if any(part.is_symlink() for part in (path, *path.parents)) or not path.is_file():
        raise ValueError(f"{label} must be a regular file without symlinks: {path}")
    return path.read_bytes()


def _verify_tree(leanvm: Path, revision: str, timeout: float, *, label: str = "Rust leanVM") -> dict[str, str]:
    """Compare worktree bytes and file modes with the pinned Git tree.

    Reading the tree rather than the index also detects modifications hidden by
    ``assume-unchanged`` or ``skip-worktree`` flags. Git environment overrides do
    not participate in selecting the repository or its objects. Replacement
    refs cannot replace the revision's tree.
    """
    leanvm = leanvm.resolve(strict=True)
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}

    def git(*args: str) -> bytes:
        return subprocess.run(
            ["git", "--no-replace-objects", *args], cwd=leanvm, env=env, check=True,
            capture_output=True, timeout=timeout,
        ).stdout

    actual_revision = git("rev-parse", "HEAD").decode().strip()
    if actual_revision != revision:
        raise ValueError(f"{label} must be at {revision}; found {actual_revision}")
    object_format = git("rev-parse", "--show-object-format").decode().strip()
    if object_format not in ("sha1", "sha256"):
        raise ValueError(f"unsupported Git object format: {object_format}")
    sources = {}
    for record in git("ls-tree", "-r", "-z", revision).split(b"\0"):
        if not record:
            continue
        metadata, raw_name = record.split(b"\t", 1)
        mode, object_kind, expected_blob = metadata.decode().split()
        name = os.fsdecode(raw_name)
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"pinned {label} tree contains an unsafe path")
        path = leanvm / relative
        parents = [path, *path.parents]
        if any(part.is_symlink() for part in parents if part != leanvm and leanvm in part.parents):
            raise ValueError(f"{label} source symlink is unsupported: {name}")
        if object_kind != "blob" or mode not in ("100644", "100755") or not path.is_file():
            raise ValueError(f"{label} source is missing or unsupported: {name}")
        executable = bool(stat.S_IMODE(path.stat().st_mode) & 0o111)
        if executable != (mode == "100755"):
            raise ValueError(f"{label} source file mode differs from the pinned tree: {name}")
        data = path.read_bytes()
        blob = hashlib.new(object_format, f"blob {len(data)}\0".encode() + data).hexdigest()
        if blob != expected_blob:
            raise ValueError(f"{label} source differs from the pinned tree: {name}")
        sources[name] = hashlib.sha256(data).hexdigest()
    return sources


def build(root: Path, leanvm: Path, build: Path, timeout: float) -> dict:
    """Return an executable descriptor after an offline, locked release build.

    ``build`` is the campaign directory. Build products remain in its ``rust``
    subdirectory; no files in either upstream checkout are modified.
    """
    root, leanvm, build = root.resolve(), leanvm.resolve(), build.resolve()
    source_hashes = _verify_tree(leanvm, REVISION, timeout)
    work = build / "rust"
    if work.is_symlink():
        raise ValueError(f"Rust build directory must not be a symlink: {work}")
    work.mkdir(parents=True, exist_ok=True)
    source = root / "tests/differential/oracle.rs"
    lock = root / "tests/oracle.Cargo.lock"
    source_data = _regular_bytes(source, "Rust adapter source")
    lock_data = _regular_bytes(lock, "Rust adapter dependency lock")
    source_sha256 = hashlib.sha256(source_data).hexdigest()
    lock_sha256 = hashlib.sha256(lock_data).hexdigest()
    for name in ("Cargo.toml", "Cargo.lock", "oracle.rs"):
        if (work / name).is_symlink():
            raise ValueError(f"Rust build input must not be a symlink: {work / name}")
    (work / "oracle.rs").write_bytes(source_data)
    manifest = f"""[package]
name = "leanisa-oracle"
version = "0.1.0"
edition = "2024"
[workspace]
[[bin]]
name = "leanisa-differential-rust"
path = {json.dumps(str(work / 'oracle.rs'))}
[dependencies]
lean_vm = {{ path = {json.dumps(str(leanvm / 'crates/lean_vm'))} }}
primitives = {{ path = {json.dumps(str(leanvm / 'crates/primitives'))} }}
serde_json = "=1.0.149"
"""
    (work / "Cargo.toml").write_text(manifest)
    (work / "Cargo.lock").write_bytes(lock_data)
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env["CARGO_TARGET_DIR"] = str(work / "target")
    env["LEANVM_NUM_THREADS"] = "1"
    # Selecting CPU features belongs to the caller; preserve its RUSTFLAGS.
    process = subprocess.run(
        ["cargo", "build", "--offline", "--locked", "--release",
         "--manifest-path", str(work / "Cargo.toml")],
        cwd=root, env=env, capture_output=True, text=True, timeout=timeout,
    )
    (work / "build.stdout").write_text(process.stdout)
    (work / "build.stderr").write_text(process.stderr)
    if process.returncode:
        raise RuntimeError(f"Rust adapter build failed; see {work / 'build.stderr'}")
    if _regular_bytes(source, "Rust adapter source") != source_data:
        raise RuntimeError("Rust adapter source changed during compilation")
    if _regular_bytes(lock, "Rust adapter dependency lock") != lock_data:
        raise RuntimeError("Rust adapter dependency lock changed during compilation")
    if _regular_bytes(work / "oracle.rs", "Staged Rust adapter source") != source_data:
        raise RuntimeError("Staged Rust adapter source changed during compilation")
    if _regular_bytes(work / "Cargo.lock", "Staged Rust adapter dependency lock") != lock_data:
        raise RuntimeError("Rust adapter dependency lock changed")
    if _verify_tree(leanvm, REVISION, timeout) != source_hashes:
        raise RuntimeError("Rust sources changed during the adapter build")
    binary = work / "target/release/leanisa-differential-rust"
    return {
        "command": [str(binary)],
        "cwd": str(root),
        "revision": REVISION,
        "source_hashes": source_hashes,
        "adapter_sha256": source_sha256,
        "lock_sha256": lock_sha256,
        "binary_sha256": _sha(binary),
        "mode": "actual-rust-apis-no-hints-no-fillers",
    }
