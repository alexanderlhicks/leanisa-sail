#!/usr/bin/env python3
"""Explicit local algebra setup and verified, offline use of its retained store."""

import argparse
from contextlib import contextmanager
import fcntl
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_STORE = ROOT / "build/dependencies/lean-algebra"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def clean_git_env(env=None):
    result = {k: v for k, v in (env or os.environ).items() if not k.startswith("GIT_")}
    result.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
                  GIT_ALLOW_PROTOCOL="", GIT_NO_LAZY_FETCH="1")
    return result


def git(repo, *args, binary=False):
    return subprocess.check_output(
        ["/usr/bin/git", "--no-replace-objects", "-c", "core.fsmonitor=false",
         "-c", "core.hooksPath=/dev/null", "-C", str(repo), *args],
        env=clean_git_env(), text=not binary, stderr=subprocess.PIPE,
    )


def load_policy(root=ROOT):
    pins = json.loads((root / "upstreams.json").read_text())
    lock_path = root / pins["mathlib"]["lock_file"]
    js_path = root / pins["mathlib"]["js_receipt_file"]
    lock = json.loads(lock_path.read_text())
    js = json.loads(js_path.read_text())
    require(type(lock["schema_version"]) is int and lock["schema_version"] == 1,
            "unknown algebra lock schema")
    packages = {p["name"]: p for p in lock["packages"]}
    require(len(packages) == len(lock["packages"]), "duplicate algebra package pin")
    require(packages["mathlib"]["revision"] == pins["mathlib"]["revision"]
            and packages["mathlib"]["url"] == pins["mathlib"]["url"],
            "Mathlib root pin differs from algebra lock")
    require(lock["root_toolchain"] == pins["lean_toolchain"],
            "algebra root toolchain differs from upstream pin")
    require(digest(js_path) == lock["js_receipt_sha256"], "JS receipt differs from lock")
    closure = {"mathlib"}
    for package in packages.values():
        for dependency in package["manifest"]["packages"]:
            name = dependency["name"]
            require(name in packages and dependency["rev"] == packages[name]["revision"]
                    and dependency["url"] == packages[name]["url"],
                    f"transitive algebra lock mismatch: {name}")
            closure.add(name)
    require(closure == set(packages), "algebra lock has missing or extra packages")
    require(js["commit"] == packages["proofwidgets"]["revision"]
            and js["lean_theorem_artifacts_extracted"] is False,
            "JS bootstrap receipt has wrong commit or theorem-artifact provenance")
    return {"lock": lock, "js": js, "root": root,
            "lock_sha256": digest(lock_path), "js_receipt_sha256": digest(js_path)}


def package_path(mathlib, name):
    return mathlib if name == "mathlib" else mathlib / ".lake/packages" / name


def owned_tree(root, boundary, *, required=False):
    """Check traversal roots and ancestors before inspecting any descendants."""
    relative = root.relative_to(boundary)
    current = boundary
    for part in (None, *relative.parts):
        if part is not None:
            current = current / part
        require(not current.is_symlink(), f"external algebra output symlink: {current}")
        require(not current.exists() or current.is_dir(),
                f"algebra output directory replaced: {current}")
    require(not required or root.is_dir(), f"missing algebra output directory: {root}")
    result = []
    for path in root.rglob("*"):
        require(not path.is_symlink(), f"external algebra output symlink: {path}")
        require(path.is_dir() or path.is_file(), f"nonregular algebra output: {path}")
        if path.is_file():
            result.append(path)
    return result


def check_output_roots(mathlib, policy):
    for package in policy["lock"]["packages"]:
        lake = package_path(mathlib, package["name"]) / ".lake"
        for name in ("build", "config"):
            owned_tree(lake / name, mathlib)


def verify_sources(mathlib, policy, *, self_contained=True, full_objects=True):
    """Check actual working bytes against tree blobs, ignoring index flags."""
    checked = []
    for package in policy["lock"]["packages"]:
        repo = package_path(mathlib, package["name"])
        require(repo.is_dir(), f"unprepared algebra dependency: missing {repo}")
        ancestry = [repo, *[p for p in repo.parents if p == mathlib or mathlib in p.parents]]
        require(not any(p.is_symlink() for p in ancestry),
                f"external algebra package symlink is forbidden: {repo}")
        require((repo / ".git").is_dir() and not (repo / ".git").is_symlink(),
                f"algebra dependency needs an owned Git directory: {repo}")
        if self_contained:
            objects = repo / ".git/objects"
            require(not (repo / ".git/commondir").exists(),
                    f"shared algebra Git directory is forbidden: {repo}")
            require(not (objects / "info/alternates").exists()
                    and not (objects / "info/http-alternates").exists(),
                    f"algebra Git alternates are forbidden: {repo}")
            require(not objects.is_symlink()
                    and not any(p.is_symlink() for p in objects.rglob("*")),
                    f"algebra Git object symlink is forbidden: {repo}")
            config_keys = git(repo, "config", "--name-only", "--list").lower().splitlines()
            require(not any(key == "extensions.partialclone"
                            or key.startswith("remote.") and key.endswith((".promisor", ".partialclonefilter"))
                            for key in config_keys)
                    and not any(objects.rglob("*.promisor")),
                    f"partial/promisor algebra Git stores are forbidden: {repo}")
            if full_objects:
                git(repo, "fsck", "--full", "--no-reflogs")
        require(git(repo, "rev-parse", "HEAD").strip() == package["revision"],
                f"algebra revision mismatch: {package['name']}")
        require((repo / "lean-toolchain").read_text() == package["toolchain_text"],
                f"algebra source toolchain mismatch: {package['name']}")
        require(digest(repo / "lake-manifest.json") == package["manifest_sha256"],
                f"algebra manifest mismatch: {package['name']}")
        require(json.loads((repo / "lake-manifest.json").read_text()) == package["manifest"],
                f"algebra nested lock mismatch: {package['name']}")
        tracked = set()
        for entry in git(repo, "ls-tree", "-rz", package["revision"], binary=True).split(b"\0"):
            if not entry:
                continue
            metadata, raw_name = entry.split(b"\t", 1)
            mode, kind, blob = metadata.split()
            relative = os.fsdecode(raw_name)
            tracked.add(relative)
            path = repo / relative
            require(kind == b"blob" and mode in (b"100644", b"100755", b"120000"),
                    f"unsupported Git source entry: {path}")
            require(not any(p.is_symlink() for p in path.parents if p != repo and repo in p.parents),
                    f"source directory symlink: {path}")
            if mode == b"120000":
                require(path.is_symlink(), f"source symlink changed: {path}")
                contents = os.fsencode(os.readlink(path))
            else:
                require(path.is_file() and not path.is_symlink(), f"source file missing: {path}")
                contents = path.read_bytes()
            actual = hashlib.sha1(b"blob " + str(len(contents)).encode() + b"\0" + contents).hexdigest()
            require(actual == blob.decode(), f"algebra source bytes changed: {path}")
        # Ignored/untracked Lean sources must not supplement the pinned module tree.
        for path in repo.rglob("*.lean"):
            relative = path.relative_to(repo)
            if relative.parts[0] not in (".git", ".lake"):
                require(str(relative) in tracked, f"untracked algebra Lean source: {path}")
        checked.append({"name": package["name"], "revision": package["revision"],
                        "url": package.get("url"),
                        "source_files": len(tracked),
                        "toolchain_text": package["toolchain_text"],
                        "manifest_sha256": package["manifest_sha256"]})
    return checked


def own_git_objects(mathlib, policy):
    """Copy object data from local alternates, then remove the external links."""
    for package in policy["lock"]["packages"]:
        repo = package_path(mathlib, package["name"])
        destination = repo / ".git/objects"
        seen = {destination.resolve()}

        def copy_alternates(objects):
            alternate_file = objects / "info/alternates"
            if not alternate_file.exists():
                return
            for line in alternate_file.read_text().splitlines():
                source = (objects / line).resolve()
                if source in seen:
                    continue
                seen.add(source)
                require(source.is_dir(), f"missing local Git objects: {source}")
                copy_alternates(source)
                for entry in source.iterdir():
                    if entry.name == "info":
                        continue
                    require(not entry.is_symlink(), f"Git object symlink: {entry}")
                    subprocess.run(["cp", "-a", "--reflink=auto", str(entry), str(destination)],
                                   check=True)
        copy_alternates(destination)
        (destination / "info/alternates").unlink(missing_ok=True)


@contextmanager
def store_lease(store):
    """One build owner at a time, including configuration cache writes."""
    store.parent.mkdir(parents=True, exist_ok=True)
    with (store.parent / (store.name + ".lock")).open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError(f"algebra dependency store is already in use: {store}") from error
        yield


@contextmanager
def offline_environment(env, directory):
    """Disable cache hooks and reject the acquisition tools used by pinned Lake."""
    directory.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="algebra-offline-", dir=directory) as tmp:
        guard = Path(tmp)
        denied = guard / "denied.log"
        script = '''#!/bin/sh
tool=${0##*/}
if [ "$tool" = git ]; then
  for arg in "$@"; do
    case "$arg" in fetch|clone|pull|push|ls-remote|submodule)
      printf '%s\\n' "$tool $*" >> "$LEANISA_ACQUISITION_LOG"; exit 97;; esac
  done
  exec /usr/bin/git "$@"
fi
printf '%s\\n' "$tool $*" >> "$LEANISA_ACQUISITION_LOG"
exit 97
'''
        for name in ("git", "curl", "wget", "npm", "npx"):
            path = guard / name
            path.write_text(script)
            path.chmod(0o755)
        guarded = clean_git_env(env)
        guarded.update(PATH=str(guard) + os.pathsep + env["PATH"],
                       LEANISA_ACQUISITION_LOG=str(denied), MATHLIB_NO_CACHE_ON_UPDATE="1",
                       LAKE_NO_CACHE="1", HTTP_PROXY="http://127.0.0.1:9",
                       HTTPS_PROXY="http://127.0.0.1:9", ALL_PROXY="http://127.0.0.1:9")
        yield guarded
        require(not denied.exists(), "algebra acquisition attempt rejected: "
                + (denied.read_text() if denied.exists() else ""))


def compiler_identity(policy, env):
    toolchain = policy["lock"]["root_toolchain"]
    env = dict(env, ELAN_TOOLCHAIN=toolchain)
    result = {"toolchain": toolchain}
    for name in ("lean", "lake"):
        path = Path(subprocess.check_output(
            ["elan", "which", name], env=env, text=True).strip())
        version = subprocess.check_output([path, "--version"], env=env, text=True).strip()
        result[name] = {"version": version, "sha256": digest(path)}
    require(policy["lock"]["compiler_commit"] in result["lean"]["version"],
            "algebra compiler commit differs from lock")
    return result


def bootstrap_js(mathlib, archive_path, policy):
    receipt = policy["js"]
    require(archive_path.stat().st_size == receipt["size"]
            and digest(archive_path) == receipt["sha256"], "ProofWidgets archive mismatch")
    destination = mathlib / ".lake/packages/proofwidgets/.lake/build"
    owned_tree(destination, mathlib)
    if (destination / "js").exists():
        shutil.rmtree(destination / "js")
    observed = set()
    with tarfile.open(archive_path) as archive:
        for member in archive.getmembers():
            path = Path(member.name)
            require(not path.is_absolute() and ".." not in path.parts,
                    f"unsafe ProofWidgets archive member: {member.name}")
            if not path.parts:
                require(member.isdir(), "invalid empty ProofWidgets archive member")
                continue
            if path.parts[0] != "js":
                continue
            require(member.isdir() or member.isfile(), "ProofWidgets JS member is not regular")
            name = path.as_posix()
            require(name not in observed, "duplicate ProofWidgets JS archive member")
            observed.add(name)
            if member.isdir():
                continue
            require(name in receipt["extracted_hashes"], "unexpected JS archive member")
            data = archive.extractfile(member).read()
            require(hashlib.sha256(data).hexdigest() == receipt["extracted_hashes"][name],
                    f"ProofWidgets JS member mismatch: {name}")
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    require(observed == set(receipt["extracted_members"]), "incomplete JS archive members")


def verify_js(store, policy):
    receipt = store / "proofwidgets-js.json"
    require(receipt.is_file() and digest(receipt) == policy["js_receipt_sha256"],
            "missing or changed ProofWidgets JS receipt")
    archive = store / "proofwidgets-js.tar.gz"
    require(archive.is_file() and digest(archive) == policy["js"]["sha256"],
            "missing or changed ProofWidgets JS archive")
    root = store / "mathlib/.lake/packages/proofwidgets/.lake/build"
    owned_tree(root, store)
    for name, expected in policy["js"]["extracted_hashes"].items():
        path = root / name
        require(path.is_file() and not path.is_symlink() and digest(path) == expected,
                f"missing or changed ProofWidgets JS member: {name}")
    actual = {str(p.relative_to(root)) for p in (root / "js").rglob("*") if p.is_file()}
    require(actual == set(policy["js"]["extracted_hashes"]), "unexpected JS bootstrap files")


def reviewed_artifacts(policy):
    reference = policy["lock"]["reviewed_cache"]
    path = policy["root"] / "dependencies" / reference["receipt_file"]
    require(digest(path) == reference["compressed_sha256"], "reviewed artifact receipt changed")
    raw = gzip.decompress(path.read_bytes())
    require(hashlib.sha256(raw).hexdigest() == reference["receipt_sha256"],
            "reviewed artifact provenance differs from pinned receipt")
    original = json.loads(raw)
    roots = [p.removesuffix("/.lake/build/lib/lean") for p in original["olean_counts"]
             if p.endswith("/mathlib/.lake/build/lib/lean")]
    require(len(roots) == 1, "ambiguous reviewed Mathlib artifact root")
    prefix = roots[0] + "/"
    return {entry["path"][len(prefix):]: {"size": entry["size"], "sha256": entry["sha256"]}
            for entry in original["artifacts"] if entry["path"].startswith(prefix)}


def verify_reviewed_artifacts(mathlib, policy):
    expected = reviewed_artifacts(policy)
    actual = set()
    for package in policy["lock"]["packages"]:
        root = package_path(mathlib, package["name"]) / ".lake/build/lib/lean"
        actual.update(str(p.relative_to(mathlib)) for p in owned_tree(root, mathlib))
    require(actual == set(expected), "reviewed Lean artifact set differs from pinned receipt")
    for relative, entry in expected.items():
        path = mathlib / relative
        require(not path.is_symlink() and path.stat().st_size == entry["size"]
                and digest(path) == entry["sha256"], f"reviewed Lean artifact changed: {relative}")


def artifact_files(mathlib, policy):
    result = []
    for package in policy["lock"]["packages"]:
        lake = package_path(mathlib, package["name"]) / ".lake"
        candidates = (owned_tree(lake / "build", mathlib)
                      + owned_tree(lake / "config", mathlib)
                      + list(lake.glob("lakefile.*")))
        for path in candidates:
            require(not path.is_symlink(), f"algebra artifact symlink: {path}")
            if path.is_file():
                result.append(path)
    return sorted(result)


def record_artifacts(mathlib, policy):
    return {str(path.relative_to(mathlib)): {"size": path.stat().st_size, "sha256": digest(path)}
            for path in artifact_files(mathlib, policy)}


def record_git_objects(mathlib, policy):
    """Fingerprint owned object files without consulting potentially altered Git data."""
    result = {}
    for package in policy["lock"]["packages"]:
        repo = package_path(mathlib, package["name"])
        ancestry = [repo, *[p for p in repo.parents if p == mathlib or mathlib in p.parents]]
        require(not any(p.is_symlink() for p in ancestry), "external algebra package symlink")
        require((repo / ".git").is_dir() and not (repo / ".git").is_symlink()
                and not (repo / ".git/commondir").exists(), "external algebra Git directory")
        objects = repo / ".git/objects"
        require(objects.is_dir() and not objects.is_symlink(), "external algebra Git objects")
        for path in sorted(objects.rglob("*")):
            require(not path.is_symlink(), "external algebra Git object symlink")
            if path.is_file():
                require(path.name not in ("alternates", "http-alternates")
                        and path.suffix != ".promisor", "external or promisor Git object metadata")
                result[str(path.relative_to(mathlib))] = {
                    "size": path.stat().st_size, "sha256": digest(path)}
    return result


def target_replay(directory, policy, env):
    args = ["lake", "--no-cache", "--no-build", "--no-ansi", "build"]
    args.extend("+" + target for target in policy["lock"]["targets"])
    subprocess.run(args, cwd=directory, env=env, check=True, capture_output=True, text=True)


def prepare_consumer(store, policy, env):
    """Reproduce production dependency indices using config-only model stubs.

    Lake resolves direct dependencies in reverse order: Mathlib is index 1,
    leanisa is index 2, then Mathlib's closure, then Sail. These stubs contain
    no Lean modules and are never dependencies of the production proof project.
    """
    consumer = store / "consumer"
    consumer.mkdir()
    model = consumer / "model"
    support = model / "support"
    support.mkdir(parents=True)
    support.joinpath("lakefile.toml").write_text('name = "Sail"\n')
    model.joinpath("lakefile.toml").write_text(
        'name = "leanisa"\n[[require]]\nname = "Sail"\npath = "support"\n')
    package = next(p for p in policy["lock"]["packages"] if p["name"] == "mathlib")
    consumer.joinpath("lakefile.toml").write_text(
        'name = "leanisa-algebra-context"\n'
        'packagesDir = "../mathlib/.lake/packages"\n'
        '[[require]]\nname = "leanisa"\npath = "model"\n'
        f'[[require]]\nname = {json.dumps(package["manifest"]["name"])}\npath = "../mathlib"\n')
    consumer.joinpath("lean-toolchain").write_text(policy["lock"]["root_toolchain"] + "\n")
    subprocess.run(["lake", "--no-cache", "update"], cwd=consumer, env=env,
                   check=True, capture_output=True, text=True)
    # A first cache creation need not create its lock file. Production `lake
    # update` may reconfigure an existing named cache, so exercise that path
    # explicitly before binding the complete file set (including its locks).
    subprocess.run(["lake", "--no-cache", "-R", "env", "true"], cwd=consumer, env=env,
                   check=True, capture_output=True, text=True)
    target_replay(consumer, policy, env)


def record_consumer(store):
    return {str(path.relative_to(store / "consumer")):
            {"size": path.stat().st_size, "sha256": digest(path)}
            for path in sorted(owned_tree(store / "consumer", store, required=True))}


def warm_replay(store, policy, env):
    # Standalone Mathlib assigns different indices to its transitive packages;
    # replay only the source-prepared, receipt-bound production-shaped context.
    target_replay(store / "consumer", policy, env)


def verify_store(store, policy=None, env=None, *, replay=True):
    """Read and verify an explicitly prepared store; this never acquires dependencies."""
    policy = policy or load_policy()
    env = dict(env or os.environ, ELAN_TOOLCHAIN=policy["lock"]["root_toolchain"])
    require((store / "receipt.json").is_file(),
            f"algebra store is unprepared: {store}; run scripts/algebra_dependencies.py setup")
    receipt = json.loads((store / "receipt.json").read_text())
    require(type(receipt["schema_version"]) is int and receipt["schema_version"] == 1
            and receipt["lock_sha256"] == policy["lock_sha256"],
            "algebra store lock receipt mismatch")
    require(receipt["mode"] in ("reviewed-source-build", "local-source-build"),
            "unsupported algebra build provenance")
    compiler = compiler_identity(policy, env)
    require(receipt["compiler"] == compiler, "algebra compiled-artifact toolchain mismatch")
    check_output_roots(store / "mathlib", policy)
    consumer_path = store / "consumer.json"
    require(consumer_path.is_file() and digest(consumer_path) == receipt["consumer_sha256"],
            "algebra consumer context receipt changed")
    consumer = json.loads(consumer_path.read_text())
    require(record_consumer(store) == consumer, "algebra consumer context changed")
    objects_path = store / "git-objects.json"
    require(objects_path.is_file() and digest(objects_path) == receipt["git_objects_sha256"],
            "algebra Git object receipt changed")
    objects = json.loads(objects_path.read_text())
    require(record_git_objects(store / "mathlib", policy) == objects,
            "algebra Git object set or contents changed")
    # Full fsck established this exact object set during setup. Check its hashes
    # before any Git tree lookup; validation never refreshes this receipt.
    packages = verify_sources(store / "mathlib", policy, full_objects=False)
    verify_js(store, policy)
    if receipt["mode"] == "reviewed-source-build":
        require(receipt["reviewed_receipt_sha256"] == policy["lock"]["reviewed_cache"]["receipt_sha256"],
                "algebra reviewed provenance mismatch")
        verify_reviewed_artifacts(store / "mathlib", policy)
    artifacts_path = store / "artifacts.json"
    require(artifacts_path.is_file() and digest(artifacts_path) == receipt["artifacts_sha256"],
            "algebra artifact receipt changed")
    artifacts = json.loads(artifacts_path.read_text())
    require(record_artifacts(store / "mathlib", policy) == artifacts,
            "algebra compiled artifact set or contents changed")
    if replay:
        with offline_environment(env, store.parent) as guarded:
            warm_replay(store, policy, guarded)
        require(record_artifacts(store / "mathlib", policy) == artifacts,
                "algebra no-build replay changed prepared artifacts")
        require(record_consumer(store) == consumer, "algebra no-build replay changed consumer context")
    return {"store": str(store.resolve()), "lock_sha256": policy["lock_sha256"], "packages": packages,
            "compiler": compiler, "mode": receipt["mode"],
            "receipt_sha256": digest(store / "receipt.json"),
            "consumer_sha256": receipt["consumer_sha256"],
            "git_objects_sha256": receipt["git_objects_sha256"], "git_object_files": len(objects),
            "artifacts_sha256": receipt["artifacts_sha256"], "artifact_files": len(artifacts),
            "js_receipt_sha256": policy["js_receipt_sha256"],
            "js_archive_sha256": policy["js"]["sha256"],
            "js_bootstrap": {k: policy["js"][k] for k in
                             ("tag", "commit", "asset_id", "url", "size",
                              "lean_theorem_artifacts_extracted")},
            "js_members": policy["js"]["extracted_hashes"], "warm_no_build": replay}


def prepare_store(sources, js_archive, store, *, reuse_reviewed_cache=False, policy=None):
    policy = policy or load_policy()
    env = dict(os.environ, ELAN_TOOLCHAIN=policy["lock"]["root_toolchain"])
    require(sources != store and sources not in store.parents,
            "algebra destination must be outside its source tree")
    check_output_roots(sources, policy)
    verify_sources(sources, policy, self_contained=False)
    compiler = compiler_identity(policy, env)
    if reuse_reviewed_cache:
        for name in ("lean", "lake"):
            reviewed = policy["lock"]["reviewed_cache"]["compiler"][name]
            require(compiler[name] == {k: reviewed[k] for k in ("version", "sha256")},
                    "reviewed artifacts require the exact accepted compiler binaries")
        verify_reviewed_artifacts(sources, policy)
    with store_lease(store):
        require(not store.exists(), f"algebra store already exists: {store}")
        temporary = Path(tempfile.mkdtemp(prefix=store.name + ".staging-", dir=store.parent))
        try:
            subprocess.run(["cp", "-a", "--reflink=auto", str(sources), str(temporary / "mathlib")], check=True)
            mathlib = temporary / "mathlib"
            own_git_objects(mathlib, policy)
            for package in policy["lock"]["packages"]:
                lake = package_path(mathlib, package["name"]) / ".lake"
                # Rebuild configuration code from checked source, not supplied cached code.
                if (lake / "config").exists():
                    shutil.rmtree(lake / "config")
                for path in lake.glob("lakefile.*"):
                    path.unlink()
                if not reuse_reviewed_cache and (lake / "build").exists():
                    shutil.rmtree(lake / "build")
            shutil.copyfile(js_archive, temporary / "proofwidgets-js.tar.gz")
            source_receipt = policy["root"] / "dependencies/proofwidgets-js.json"
            shutil.copyfile(source_receipt, temporary / "proofwidgets-js.json")
            bootstrap_js(mathlib, temporary / "proofwidgets-js.tar.gz", policy)
            verify_sources(mathlib, policy)
            with offline_environment(env, temporary) as guarded:
                if not reuse_reviewed_cache:
                    args = ["lake", "--no-cache", "--no-ansi", "build"]
                    args.extend("+" + target for target in policy["lock"]["targets"])
                    subprocess.run(args, cwd=mathlib, env=guarded, check=True)
                # Regenerate the root context, then the production dependency
                # context. Only the latter is replayed during ordinary use.
                target_replay(mathlib, policy, guarded)
                prepare_consumer(temporary, policy, guarded)
            consumer = temporary / "consumer.json"
            consumer.write_text(json.dumps(record_consumer(temporary), indent=2) + "\n")
            artifacts = temporary / "artifacts.json"
            artifacts.write_text(json.dumps(record_artifacts(mathlib, policy), indent=2) + "\n")
            objects = temporary / "git-objects.json"
            objects.write_text(json.dumps(record_git_objects(mathlib, policy), indent=2) + "\n")
            receipt = {"schema_version": 1, "lock_sha256": policy["lock_sha256"],
                       "mode": "reviewed-source-build" if reuse_reviewed_cache else "local-source-build",
                       "compiler": compiler, "artifacts_sha256": digest(artifacts),
                       "consumer_sha256": digest(consumer),
                       "git_objects_sha256": digest(objects),
                       "reviewed_receipt_sha256": policy["lock"]["reviewed_cache"]["receipt_sha256"]
                       if reuse_reviewed_cache else None}
            (temporary / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
            verify_store(temporary, policy, env)
            temporary.rename(store)
            return verify_store(store, policy, env)
        finally:
            if temporary.exists():
                shutil.rmtree(temporary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("setup", "verify"))
    parser.add_argument("--store", type=Path, default=DEFAULT_STORE)
    parser.add_argument("--sources", type=Path, help="local pinned Mathlib tree including its eight packages")
    parser.add_argument("--js-archive", type=Path, help="exact official ProofWidgets v0.0.95 archive")
    parser.add_argument("--reuse-reviewed-cache", action="store_true",
                        help="reuse only artifacts matching the pinned reviewed source-build receipt")
    args = parser.parse_args()
    store = args.store.resolve()
    if args.action == "setup":
        require(args.sources is not None and args.js_archive is not None,
                "setup requires --sources and --js-archive; no downloads are performed")
        result = prepare_store(args.sources.resolve(), args.js_archive.resolve(), store,
                               reuse_reviewed_cache=args.reuse_reviewed_cache)
    else:
        with store_lease(store):
            result = verify_store(store)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
