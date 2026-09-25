"""Small offline protocol regressions; no Mathlib cold build or network access."""

import copy
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tarfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import algebra_dependencies as algebra
import check


class SourceIntegrityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "mathlib"
        self.repo.mkdir()
        subprocess.run(["git", "init", "-q", self.repo], check=True)
        (self.repo / "lean-toolchain").write_text("leanprover/lean4:v4.29.0\n")
        (self.repo / "lake-manifest.json").write_text('{"packages":[]}\n')
        (self.repo / "Fixture.lean").write_text("def fixture : Nat := 7\n")
        algebra.git(self.repo, "add", ".")
        algebra.git(self.repo, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                    "commit", "-qm", "fixture")
        self.policy = {"lock": {"packages": [{
            "name": "mathlib", "revision": algebra.git(self.repo, "rev-parse", "HEAD").strip(),
            "toolchain_text": (self.repo / "lean-toolchain").read_text(),
            "manifest_sha256": algebra.digest(self.repo / "lake-manifest.json"),
            "manifest": {"packages": []},
        }]}}

    def test_exact_sources_and_nested_toolchain_text(self):
        result = algebra.verify_sources(self.repo, self.policy)
        self.assertEqual(result[0]["source_files"], 3)
        bad = copy.deepcopy(self.policy)
        bad["lock"]["packages"][0]["toolchain_text"] = "leanprover/lean4:v4.27.0-rc1\n"
        with self.assertRaisesRegex(RuntimeError, "toolchain mismatch"):
            algebra.verify_sources(self.repo, bad)

    def test_wrong_revision_and_manifest_fail(self):
        bad = copy.deepcopy(self.policy)
        bad["lock"]["packages"][0]["revision"] = "0" * 40
        with self.assertRaisesRegex(RuntimeError, "revision mismatch"):
            algebra.verify_sources(self.repo, bad)
        (self.repo / "lake-manifest.json").write_text('{"packages":["wrong"]}\n')
        with self.assertRaisesRegex(RuntimeError, "manifest mismatch"):
            algebra.verify_sources(self.repo, self.policy)

    def test_skip_worktree_does_not_hide_source_changes(self):
        algebra.git(self.repo, "update-index", "--skip-worktree", "Fixture.lean")
        (self.repo / "Fixture.lean").write_text("def fixture : Nat := 8\n")
        self.assertEqual(algebra.git(self.repo, "status", "--porcelain"), "")
        algebra.git(self.repo, "diff", "--quiet", "HEAD")
        with self.assertRaisesRegex(RuntimeError, "source bytes changed"):
            algebra.verify_sources(self.repo, self.policy)

    def test_object_alternates_and_package_symlinks_fail(self):
        alternate = self.repo / ".git/objects/info/alternates"
        alternate.write_text(str(self.root / "elsewhere") + "\n")
        with self.assertRaisesRegex(RuntimeError, "alternates"):
            algebra.verify_sources(self.repo, self.policy)
        alternate.unlink()
        alias = self.root / "alias"
        alias.symlink_to(self.repo, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, "package symlink"):
            algebra.verify_sources(alias, self.policy)

    def test_inherited_git_settings_are_removed(self):
        hostile = {"PATH": "/usr/bin", "GIT_ALTERNATE_OBJECT_DIRECTORIES": "/external",
                   "GIT_DIR": "/external/repo", "GIT_WORK_TREE": "/external/tree"}
        clean = algebra.clean_git_env(hostile)
        self.assertNotIn("GIT_ALTERNATE_OBJECT_DIRECTORIES", clean)
        self.assertNotIn("GIT_DIR", clean)
        self.assertNotIn("GIT_WORK_TREE", clean)
        self.assertEqual(clean["GIT_ALLOW_PROTOCOL"], "")

    def test_promisor_repository_cannot_claim_object_completeness(self):
        algebra.git(self.repo, "config", "remote.origin.promisor", "true")
        with self.assertRaisesRegex(RuntimeError, "partial/promisor"):
            algebra.verify_sources(self.repo, self.policy)
        algebra.git(self.repo, "config", "--unset", "remote.origin.promisor")
        marker = self.repo / ".git/objects/pack/untrusted.promisor"
        marker.write_text("")
        with self.assertRaisesRegex(RuntimeError, "partial/promisor"):
            algebra.verify_sources(self.repo, self.policy)

    def test_object_receipt_checked_before_git_reads_and_never_refreshed(self):
        policy = copy.deepcopy(self.policy)
        policy.update(lock_sha256="locked", js_receipt_sha256="js-receipt", js={
            "sha256": "archive", "extracted_hashes": {}, "tag": "tag", "commit": "commit",
            "asset_id": 1, "url": "fixture", "size": 0,
            "lean_theorem_artifacts_extracted": False})
        policy["lock"]["root_toolchain"] = "fixture"
        objects_path = self.root / "git-objects.json"
        objects_path.write_text(json.dumps(algebra.record_git_objects(self.repo, policy)))
        artifacts_path = self.root / "artifacts.json"
        artifacts_path.write_text("{}")
        receipt_path = self.root / "receipt.json"
        receipt_path.write_text(json.dumps({
            "schema_version": 1, "lock_sha256": "locked", "compiler": {},
            "mode": "local-source-build", "git_objects_sha256": algebra.digest(objects_path),
            "consumer_sha256": algebra.digest(artifacts_path),
            "artifacts_sha256": algebra.digest(artifacts_path)}))
        (self.root / "consumer").mkdir()
        (self.root / "consumer.json").write_text("{}")
        original_objects = objects_path.read_bytes()
        original_receipt = receipt_path.read_bytes()
        object_file = self.repo / next(iter(json.loads(original_objects)))
        original_object = object_file.read_bytes()
        object_file.chmod(0o644)
        added = self.repo / ".git/objects/unexpected"
        with patch.object(algebra, "compiler_identity", return_value={}), \
             patch.object(algebra, "verify_sources", return_value=[]) as sources, \
             patch.object(algebra, "verify_js"), \
             patch.object(algebra, "record_artifacts", return_value={}):
            for _ in range(2):
                algebra.verify_store(self.root, policy, replay=False)
                self.assertFalse(sources.call_args.kwargs["full_objects"])
                self.assertEqual(objects_path.read_bytes(), original_objects)
                self.assertEqual(receipt_path.read_bytes(), original_receipt)
            for mutation in ("added", "removed", "changed", "manifest", "receipt"):
                with self.subTest(mutation=mutation):
                    sources.reset_mock()
                    if mutation == "added":
                        added.write_bytes(b"unrecorded")
                    elif mutation == "removed":
                        object_file.unlink()
                    elif mutation == "changed":
                        object_file.write_bytes(bytes([original_object[0] ^ 1]) + original_object[1:])
                    elif mutation == "manifest":
                        objects_path.write_text("{}")
                    else:
                        receipt = json.loads(original_receipt)
                        receipt["git_objects_sha256"] = "0" * 64
                        receipt_path.write_text(json.dumps(receipt))
                    before_objects = objects_path.read_bytes()
                    before_receipt = receipt_path.read_bytes()
                    with self.assertRaisesRegex(RuntimeError, "Git object"):
                        algebra.verify_store(self.root, policy, replay=False)
                    sources.assert_not_called()
                    self.assertEqual(objects_path.read_bytes(), before_objects)
                    self.assertEqual(receipt_path.read_bytes(), before_receipt)
                    added.unlink(missing_ok=True)
                    object_file.write_bytes(original_object)
                    objects_path.write_bytes(original_objects)
                    receipt_path.write_bytes(original_receipt)
class PreparationProtocolTests(unittest.TestCase):
    def test_output_roots_and_ancestors_reject_symlinks_before_traversal(self):
        for prefix in ("", ".lake/packages/dep/"):
            for ancestor in (".lake", ".lake/build", ".lake/config", ".lake/build/lib"):
                with self.subTest(prefix=prefix, ancestor=ancestor), tempfile.TemporaryDirectory() as tmp:
                    boundary = Path(tmp) / "mathlib"
                    root = boundary / prefix / ancestor
                    root.mkdir(parents=True)
                    target = root / "child"
                    target.mkdir()
                    (target / "output").write_bytes(b"same output")
                    external = Path(tmp) / "external"
                    root.rename(external)
                    root.symlink_to(external, target_is_directory=True)
                    with patch.object(Path, "rglob") as walk:
                        with self.assertRaisesRegex(RuntimeError, "output symlink"):
                            algebra.owned_tree(target, boundary, required=True)
                        walk.assert_not_called()
                    root.unlink()
                    with self.assertRaisesRegex(RuntimeError, "missing algebra output"):
                        algebra.owned_tree(target, boundary, required=True)
                    root.write_bytes(b"not a directory")
                    with self.assertRaisesRegex(RuntimeError, "directory replaced"):
                        algebra.owned_tree(target, boundary, required=True)

    def test_store_requires_exclusive_ownership(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = Path(tmp) / "store"
            with algebra.store_lease(store):
                with self.assertRaisesRegex(RuntimeError, "already in use"):
                    with algebra.store_lease(store):
                        self.fail("second owner entered")

    def test_acquisition_attempt_cannot_be_ignored(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(RuntimeError, "acquisition attempt"):
                with algebra.offline_environment(dict(os.environ), Path(tmp)) as env:
                    result = subprocess.run(["curl", "https://example.invalid"], env=env)
                    self.assertEqual(result.returncode, 97)

    def test_missing_store_removes_previous_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            (build / "validation.json").write_text('{"stale":"success"}')
            with self.assertRaisesRegex(RuntimeError, "unprepared"):
                check.check_lean_proofs(build / "unused-model", build, dict(os.environ),
                                       "leanprover/lean4:v4.29.0", algebra_store=build / "absent")
            self.assertFalse((build / "validation.json").exists())

    def test_js_receipt_and_member_integrity(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = Path(tmp)
            js = store / "mathlib/.lake/packages/proofwidgets/.lake/build/js"
            js.mkdir(parents=True)
            (js / "lake.trace").write_bytes(b"original trace")
            (store / "proofwidgets-js.json").write_bytes(b"exact receipt")
            (store / "proofwidgets-js.tar.gz").write_bytes(b"exact archive")
            policy = {"js_receipt_sha256": algebra.digest(store / "proofwidgets-js.json"),
                      "js": {"sha256": algebra.digest(store / "proofwidgets-js.tar.gz"),
                             "extracted_hashes": {"js/lake.trace": algebra.digest(js / "lake.trace")}}}
            algebra.verify_js(store, policy)
            (js / "lake.trace").write_bytes(b"changed trace")
            with self.assertRaisesRegex(RuntimeError, "JS member"):
                algebra.verify_js(store, policy)
            (js / "lake.trace").write_bytes(b"original trace")
            (store / "proofwidgets-js.json").unlink()
            with self.assertRaisesRegex(RuntimeError, "JS receipt"):
                algebra.verify_js(store, policy)

    def test_changed_compiled_artifact_is_detected(self):
        with tempfile.TemporaryDirectory() as tmp:
            mathlib = Path(tmp)
            path = mathlib / ".lake/build/lib/lean/Fixture.olean"
            path.parent.mkdir(parents=True)
            path.write_bytes(b"locally built object")
            policy = {"lock": {"packages": [{"name": "mathlib"}]}}
            before = algebra.record_artifacts(mathlib, policy)
            path.write_bytes(b"changed built object")
            self.assertNotEqual(algebra.record_artifacts(mathlib, policy), before)


class RealLakeConfigurationTests(unittest.TestCase):
    """Use real pinned Lake/Git and tiny source builds, including poisoned caches."""

    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="algebra-real-lake-")
        cls.addClassCleanup(cls.temp.cleanup)
        cls.root = Path(cls.temp.name)
        cls.repo = cls.root / "input/mathlib"
        cls.repo.mkdir(parents=True)
        cls.env = dict(os.environ, ELAN_TOOLCHAIN="leanprover/lean4:v4.29.0")
        cls.normal = ('import Lake\nopen Lake DSL\npackage fixture\nlean_lib Fixture\n'
                      'script witness do\n  IO.println "SOURCE_CONFIG"\n  return 0\n')
        (cls.repo / "lakefile.lean").write_text(cls.normal)
        (cls.repo / "lean-toolchain").write_text(cls.env["ELAN_TOOLCHAIN"] + "\n")
        (cls.repo / "Fixture.lean").write_text('theorem fixture : 1 + 1 = 2 := rfl\n')
        cls.run_lake(cls.repo, "update")
        cls.run_lake(cls.repo, "build", "+Fixture:olean")
        (cls.repo / ".gitignore").write_text('.lake/\n')
        subprocess.run(["git", "init", "-q", cls.repo], check=True)
        algebra.git(cls.repo, "add", ".")
        algebra.git(cls.repo, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                    "commit", "-qm", "source configuration")
        package = {"name": "mathlib", "revision": algebra.git(cls.repo, "rev-parse", "HEAD").strip(),
                   "url": "local", "toolchain_text": (cls.repo / "lean-toolchain").read_text(),
                   "manifest_sha256": algebra.digest(cls.repo / "lake-manifest.json"),
                   "manifest": json.loads((cls.repo / "lake-manifest.json").read_text())}
        metadata = cls.root / "metadata"
        (metadata / "dependencies").mkdir(parents=True)
        cls.archive = cls.root / "js.tar.gz"
        data = b"fixture JS trace\n"
        with tarfile.open(cls.archive, "w:gz") as archive:
            member = tarfile.TarInfo("js")
            member.type = tarfile.DIRTYPE
            archive.addfile(member)
            member = tarfile.TarInfo("js/lake.trace")
            member.size = len(data)
            archive.addfile(member, io.BytesIO(data))
        js = {"sha256": algebra.digest(cls.archive), "size": cls.archive.stat().st_size,
              "extracted_hashes": {"js/lake.trace": hashlib.sha256(data).hexdigest()},
              "extracted_members": ["js", "js/lake.trace"], "tag": "fixture", "commit": "fixture",
              "asset_id": 0, "url": "fixture", "lean_theorem_artifacts_extracted": False}
        js_receipt = metadata / "dependencies/proofwidgets-js.json"
        js_receipt.write_text(json.dumps(js))
        cls.policy = {"root": metadata, "lock_sha256": "fixture",
                      "js_receipt_sha256": algebra.digest(js_receipt), "js": js,
                      "lock": {"packages": [package], "root_toolchain": cls.env["ELAN_TOOLCHAIN"],
                               "compiler_commit": "98dc76e3c0a9b856c9b98726b713fb04fab16740",
                               "targets": ["Fixture:olean"]}}
        algebra.prepare_consumer(cls.repo.parent, cls.policy, cls.env)
        cls.contexts = ["[anonymous]", "fixture"]
        traces = {name: (cls.repo / f".lake/config/{name}/lakefile.olean.trace").read_bytes()
                  for name in cls.contexts}
        (cls.repo / "lakefile.lean").write_text(cls.normal.replace("SOURCE_CONFIG", "WRONG_CACHED_CONFIG"))
        cls.run_lake(cls.repo, "-R", "env", "true")
        cls.run_lake(cls.repo.parent / "consumer", "-R", "env", "true")
        cls.bad_caches = {name: (cls.repo / f".lake/config/{name}/lakefile.olean").read_bytes()
                          for name in cls.contexts}
        (cls.repo / "lakefile.lean").write_text(cls.normal)
        for name, trace in traces.items():
            (cls.repo / f".lake/config/{name}/lakefile.olean.trace").write_bytes(trace)
        if cls.run_lake(cls.repo, "run", "witness").strip() != "WRONG_CACHED_CONFIG":
            raise RuntimeError("fixture did not reproduce source/cache disagreement")
        cls.store = cls.root / "store"
        cls.prepared = algebra.prepare_store(cls.repo, cls.archive, cls.store, policy=cls.policy)

    @classmethod
    def run_lake(cls, directory, *args):
        result = subprocess.run(["lake", "--no-cache", *args], cwd=directory, env=cls.env,
                                text=True, capture_output=True, check=True, timeout=60)
        return result.stdout

    def test_setup_rebuilds_root_and_named_configuration_from_source(self):
        self.assertEqual(self.run_lake(self.store / "mathlib", "run", "witness").strip(), "SOURCE_CONFIG")
        self.assertEqual(self.run_lake(self.store / "consumer", "run", "fixture/witness").strip(), "SOURCE_CONFIG")
        before = (self.store / "artifacts.json").read_bytes()
        # Production stages a new proof project and runs `lake update`; this
        # must not introduce even an empty lock file after setup has frozen it.
        self.run_lake(self.store / "consumer", "update")
        self.run_lake(self.store / "consumer", "--no-build", "build", "+Fixture:olean")
        first = algebra.verify_store(self.store, self.policy)
        second = algebra.verify_store(self.store, self.policy)
        self.assertEqual(first, second)
        self.assertEqual((self.store / "artifacts.json").read_bytes(), before)

    def test_configuration_mutations_fail_before_lake_and_preserve_receipts(self):
        preserved = {name: (self.store / name).read_bytes()
                     for name in ("receipt.json", "artifacts.json", "consumer.json")}
        for context in self.contexts:
            for suffix in ("", ".trace", ".lock"):
                with self.subTest(context=context, suffix=suffix):
                    path = self.store / f"mathlib/.lake/config/{context}/lakefile.olean{suffix}"
                    original = path.read_bytes() if path.exists() else None
                    try:
                        path.write_bytes(self.bad_caches[context] if not suffix else b"changed metadata")
                        with patch.object(algebra, "warm_replay") as replay:
                            with self.assertRaisesRegex(RuntimeError, "compiled artifact"):
                                algebra.verify_store(self.store, self.policy)
                            replay.assert_not_called()
                        build = self.root / "failure-build"
                        build.mkdir(exist_ok=True)
                        (build / "validation.json").write_text('{"stale":"success"}')
                        with patch.object(algebra, "load_policy", return_value=self.policy):
                            with self.assertRaisesRegex(RuntimeError, "compiled artifact"):
                                check.check_lean_proofs(self.root / "unused-model", build, self.env,
                                                       self.env["ELAN_TOOLCHAIN"], algebra_store=self.store)
                        self.assertFalse((build / "validation.json").exists())
                    finally:
                        if original is None:
                            path.unlink()
                        else:
                            path.write_bytes(original)
                    self.assertEqual({name: (self.store / name).read_bytes() for name in preserved}, preserved)
        for relative in ("mathlib/.lake/config/extra/lakefile.olean", "mathlib/.lake/build/lib/unexpected.so",
                         "consumer/model/Injected.lean"):
            with self.subTest(addition=relative):
                path = self.store / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b"unrecorded executable input")
                try:
                    with patch.object(algebra, "warm_replay") as replay:
                        with self.assertRaisesRegex(RuntimeError, "artifact|consumer context"):
                            algebra.verify_store(self.store, self.policy)
                        replay.assert_not_called()
                finally:
                    path.unlink()

    def test_identical_external_outputs_rejected_by_setup_and_verification(self):
        for relative in ("mathlib/.lake/build", "mathlib/.lake/config", "consumer"):
            with self.subTest(root=relative):
                path = self.store / relative
                external = self.root / "borrowed"
                path.rename(external)
                path.symlink_to(external, target_is_directory=True)
                try:
                    with patch.object(algebra, "warm_replay") as replay:
                        with self.assertRaisesRegex(RuntimeError, "output symlink"):
                            algebra.verify_store(self.store, self.policy)
                        replay.assert_not_called()
                    if relative.startswith("mathlib"):
                        with patch.object(subprocess, "run") as execution:
                            with self.assertRaisesRegex(RuntimeError, "output symlink"):
                                algebra.prepare_store(self.store / "mathlib", self.archive,
                                                      self.root / "rejected", policy=self.policy)
                            execution.assert_not_called()
                finally:
                    path.unlink()
                    external.rename(path)

    def test_missing_configuration_and_changed_consumer_fail_before_lake(self):
        relatives = [f"mathlib/.lake/config/{context}/lakefile.olean" for context in self.contexts]
        relatives.append("consumer/lakefile.toml")
        receipt = (self.store / "receipt.json").read_bytes()
        for relative in relatives:
            with self.subTest(path=relative):
                path = self.store / relative
                original = path.read_bytes()
                try:
                    if path.suffix == ".olean":
                        path.unlink()
                    else:
                        path.write_bytes(original + b"\n# changed context\n")
                    with patch.object(algebra, "warm_replay") as replay:
                        with self.assertRaisesRegex(RuntimeError, "artifact|consumer context"):
                            algebra.verify_store(self.store, self.policy)
                        replay.assert_not_called()
                    self.assertEqual((self.store / "receipt.json").read_bytes(), receipt)
                finally:
                    path.write_bytes(original)


if __name__ == "__main__":
    unittest.main()
