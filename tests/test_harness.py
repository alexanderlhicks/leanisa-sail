"""Harness regressions; also run with python3 -O -m unittest discover -s tests."""

import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import check

ORACLE = check.ROOT / "build/cargo/release/leanisa-oracle"
MODEL_PROJECT = check.ROOT / "build/generated-lean/leanisa"
FIXTURES = json.loads((check.ROOT / "tests/replay.json").read_text())


class AcceptanceTests(unittest.TestCase):
    def test_solver_must_report_exactly_unsat(self):
        for output in ("sat\n", "unknown\n", "", "timeout\n", "unsat\nsat\n"):
            with (
                self.subTest(output=output),
                self.assertRaisesRegex(RuntimeError, "expected unsat"),
            ):
                check.require_unsat(
                    "false_property", subprocess.CompletedProcess([], 0, output, "")
                )
        check.require_unsat(
            "true_property", subprocess.CompletedProcess([], 0, "unsat\n", "")
        )

    def test_backend_must_report_pass(self):
        for output in ("", "did not print leanISA validation: PASS", "FAIL"):
            with (
                self.subTest(output=output),
                self.assertRaisesRegex(RuntimeError, "did not report PASS"),
            ):
                check.require_pass("C", output)

    def test_incorrect_rust_arithmetic_is_rejected(self):
        req = {"kind": "field", "a": check.limbs(1), "b": check.limbs(1)}
        for answer in (
            {"base": "0", "extension": check.limbs(1)},
            {"base": "1", "extension": check.limbs(0)},
        ):
            with (
                self.subTest(answer=answer),
                self.assertRaisesRegex(RuntimeError, "Rust/Python"),
            ):
                check.source([req], [answer])

    def test_incorrect_rust_hash_is_rejected(self):
        req = {
            "kind": "blake",
            "message": ["0"] * 8,
            "cv": ["0"] * 4,
            "md": check.limbs(0),
            "hashlib": "ff" * 32,
        }
        with self.assertRaisesRegex(RuntimeError, "Rust/hashlib"):
            check.source([req], [["0"] * 4])

    def test_large_address_translation_is_logarithmic(self):
        a = 1
        for offset in range(256):
            self.assertEqual(check.address(offset), check.hx(a))
            a = check.polynomial_mul(a, 2)
        self.assertEqual(
            int(check.address(check.U32_MAX), 16),
            check.polynomial_mul(int(check.address(check.U32_MAX - 1), 16), 2),
        )

    def test_out_of_domain_inputs_are_rejected(self):
        for offset in (-1, 1 << 32, True, 1.5, "0"):
            req = copy.deepcopy(FIXTURES[1])
            req["program"][0][1] = offset
            with (
                self.subTest(offset=offset),
                self.assertRaisesRegex(RuntimeError, "offset"),
            ):
                check.validate_request(req)
        req = copy.deepcopy(FIXTURES[0])
        req["input"][0][2] = "1"
        with self.assertRaisesRegex(RuntimeError, "128 bits"):
            check.validate_request(req)

    def test_wrong_version_pins_are_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            support = Path(tmp)
            (support / "lean-toolchain").write_text("leanprover/lean4:v4.29.0")
            pins = {"z3": "4.15.4", "lean_toolchain": "leanprover/lean4:v4.29.0"}
            z3 = subprocess.CompletedProcess([], 0, "Z3 version 4.15.4 - 64 bit\n", "")
            with patch.object(check, "command", return_value=z3):
                for key in pins:
                    bad_pins = dict(pins, **{key: "0.0.0"})
                    with (
                        self.subTest(key=key),
                        self.assertRaisesRegex(RuntimeError, "differs"),
                    ):
                        check.check_tool_versions(bad_pins, support, {}, lean=False)
            lean = subprocess.CompletedProcess(
                [], 0, "Lean (version 0.0.0, fake)\n", ""
            )
            with patch.object(check, "command", side_effect=[z3, lean]):
                with self.assertRaisesRegex(RuntimeError, "Lean executable differs"):
                        check.check_tool_versions(pins, support, {}, lean=True)

    def test_axiom_audit_requires_complete_consistent_success(self):
        good = {
            "schema_version": 1,
            "status": "pass",
            "allowed_axioms": check.ALLOWED_LEAN_AXIOMS,
            "checked_declarations": 1,
            "modules": [
                {"module": "Owned", "declarations": 1,
                 "axioms": ["propext"], "violations": []},
                {"module": "Empty", "declarations": 0,
                 "axioms": [], "violations": []},
            ],
        }
        check.validate_axiom_audit(good, ["Owned", "Empty"])
        bad_reports = [None, {}, dict(good, status="fail"),
                       dict(good, schema_version=True),
                       dict(good, allowed_axioms=["propext"]),
                       dict(good, checked_declarations=2),
                       dict(good, checked_declarations=True),
                       dict(good, modules=good["modules"][:1]),
                       dict(good, modules=good["modules"] * 2)]
        for replacement in (
            {"declarations": True}, {"declarations": -1},
            {"module": "OtherNamespace"}, {"axioms": ["Other.propext"]},
            {"axioms": None}, {"axioms": ["propext", "propext"]},
            {"violations": [{"declaration": "hidden", "axioms": ["secret"]}]},
        ):
            bad = copy.deepcopy(good)
            bad["modules"][0].update(replacement)
            bad_reports.append(bad)
        for report in bad_reports:
            with self.subTest(report=report), self.assertRaises(RuntimeError):
                check.validate_axiom_audit(report, ["Owned", "Empty"])
        contradictory = copy.deepcopy(good)
        contradictory["modules"][0]["declarations"] = 0
        contradictory["checked_declarations"] = 0
        with self.assertRaisesRegex(RuntimeError, "empty module"):
            check.validate_axiom_audit(contradictory, ["Owned", "Empty"])

    def test_missing_axiom_audit_cannot_reuse_stale_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            destination = Path(tmp)
            (destination / "axiom-audit.json").write_text('{"status":"pass"}')
            with patch.object(check, "command"):
                with self.assertRaisesRegex(RuntimeError, "did not produce a report"):
                    check.audit_lean_proofs(destination, ["Owned"], {})
            self.assertFalse((destination / "axiom-audit.json").exists())

    def test_malformed_axiom_audit_json_is_rejected(self):
        for text in ("{", "null", '{"status":"fail","status":"pass"}'):
            with self.subTest(text=text), tempfile.TemporaryDirectory() as tmp:
                destination = Path(tmp)

                def write_report(*args, **kwargs):
                    (destination / "axiom-audit.json").write_text(text)

                with patch.object(check, "command", side_effect=write_report):
                    with self.assertRaises(RuntimeError):
                        check.audit_lean_proofs(destination, ["Owned"], {})


@unittest.skipUnless(
    ORACLE.exists(), "build the Rust oracle with scripts/check.py first"
)
class OracleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.build = Path(self.temp.name)
        self.env = dict(os.environ, LEANVM_NUM_THREADS="1")

    def raw(self, req):
        output = check.command(
            [ORACLE], env=self.env, capture=True, data=json.dumps(req) + "\n", timeout=5
        ).stdout
        return json.loads(output)

    def run_cases(self, cases, timeout=5):
        return check.run_oracle(
            cases, ORACLE, env=self.env, build=self.build, timeout=timeout
        )

    def test_singleton_unused_cell_and_contract_regressions(self):
        answers = self.run_cases(FIXTURES)
        self.assertEqual([a["cycles"] for a in answers[:3]], [0, 1, 3])
        generated = check.source(FIXTURES, answers)
        self.assertNotIn(", -1)", generated)
        self.assertIn('== Halted, "mutation 1 cell 4"', generated)
        self.assertIn('== BadValue, "execution 2"', generated)
        # Removing explicit mutations must not introduce template-based ones.
        no_mutations = copy.deepcopy(FIXTURES[1])
        no_mutations.pop("mutations")
        self.assertNotIn("mutation", check.source([no_mutations], [answers[1]]))

    def test_unconstrained_reads_cannot_certify_image_acceptance(self):
        bad, good = self.run_cases([FIXTURES[2], FIXTURES[3]])
        self.assertEqual(bad["unconstrained_reads"], [])
        self.assertEqual(good["unconstrained_reads"], [2, 3])
        bad["unconstrained_reads"] = [2]
        with self.assertRaisesRegex(RuntimeError, "unconstrained_reads diagnostic"):
            check.source([FIXTURES[2]], [bad])

    def test_rust_parser_does_not_truncate_offsets(self):
        for offset in (-1, 1 << 32, True):
            req = copy.deepcopy(FIXTURES[1])
            req["program"][0][1] = offset
            reply = self.raw(req)
            self.assertEqual(reply["status"], "rejected")
            self.assertIn("offset", reply["error"])

    def test_rust_rejects_malformed_words_and_modes(self):
        for value in ([], ["1"] * 4, ["10000000000000000", "0", "0"]):
            reply = self.raw({"kind": "field", "a": value, "b": check.limbs(0)})
            self.assertEqual(reply["status"], "rejected")
        req = copy.deepcopy(FIXTURES[1])
        req["program"][0] = ["deref", 0, 0, 0, "invalid"]
        self.assertEqual(self.raw(req)["status"], "rejected")

    def test_invalid_input_is_preserved_before_launch(self):
        req = copy.deepcopy(FIXTURES[1])
        req["program"][0][1] = 1 << 32
        with patch.object(check, "command") as launch:
            with self.assertRaisesRegex(RuntimeError, "invalid_input"):
                self.run_cases([req])
            launch.assert_not_called()
        failure = json.loads((self.build / "oracle-failure.json").read_text())
        self.assertEqual(failure["request"], req)

    def test_loop_is_killed_and_preserved(self):
        req = {
            "kind": "execute",
            "input": [check.limbs(1), check.limbs(0)],
            "program": [["jump", 0, 0, 0], ["xor", 0, 0, 0]],
        }
        with self.assertRaisesRegex(RuntimeError, "timeout"):
            self.run_cases([req], timeout=0.1)
        failure = json.loads((self.build / "oracle-failure.json").read_text())
        self.assertEqual(failure["request"], req)
        self.assertEqual(failure["status"], "timeout")
        self.assertFalse((self.build / "validation.json").exists())

    def test_upstream_panic_is_separate_from_rejection(self):
        req = {
            "kind": "execute",
            "input": [check.limbs(0), check.limbs(0)],
            "program": [["set", 0, check.limbs(1)], ["xor", 0, 0, 0]],
        }
        self.assertEqual(self.raw(req)["status"], "panic")
        with self.assertRaisesRegex(RuntimeError, "panic"):
            self.run_cases([req])
        failure = json.loads((self.build / "oracle-failure.json").read_text())
        self.assertEqual(failure["request"], req)


@unittest.skipUnless(
    (check.ROOT / "build/lean-proofs/lakefile.toml").exists(),
    "build the Lean model and proof library with scripts/check.py first",
)
class ProofTests(unittest.TestCase):
    def test_axiom_policy_covers_all_owned_declarations(self):
        """Real Lean fixtures, including unused/private/native declarations."""
        real_command = check.command

        def captured_command(args, **kwargs):
            return real_command(args, **dict(kwargs, capture=True, timeout=60))

        toolchain = (MODEL_PROJECT / "lean-toolchain").read_text().strip()
        env = dict(os.environ, ELAN_TOOLCHAIN=toolchain)
        allowed = """import Lean
namespace UnrelatedNamespace
theorem logical_eq {p q : Prop} (h : p ↔ q) : p = q := propext h
noncomputable def choose (α : Type) (h : Nonempty α) : α := Classical.choice h
theorem quotient_eq (r : Nat → Nat → Prop) (a b : Nat) (h : r a b) :
    Quot.mk r a = Quot.mk r b := Quot.sound h
end UnrelatedNamespace
"""
        probes = (
            ("import Lean\naxiom unused_external : Nat\n", "unused_external"),
            ("import Lean\naxiom unsupported : False\n"
             "theorem derived_false : False := unsupported\n", "derived_false"),
            ("import Lean\nprivate axiom private_hidden : Nat\n", "private_hidden"),
            ("module\nprivate axiom module_hidden : Nat\n", "module_hidden"),
            ("import Lean\ntheorem compiled : (1 : Nat) = 1 := by native_decide\n",
             "native_decide"),
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "proofs").mkdir()
            (root / "proofs/Empty.lean").write_text("import Lean\n")
            source = root / "proofs/Owned.lean"
            source.write_text(allowed)
            with (patch.object(check, "ROOT", root),
                  patch.object(check, "command", side_effect=captured_command)):
                result = check.check_lean_proofs(MODEL_PROJECT, root, env, toolchain)
            audit = result["axiom_audit"]
            self.assertEqual([m["module"] for m in audit["modules"]], ["Empty", "Owned"])
            self.assertEqual(audit["modules"][0]["declarations"], 0)
            self.assertGreaterEqual(audit["modules"][1]["declarations"], 3)
            self.assertEqual(audit["modules"][1]["axioms"], check.ALLOWED_LEAN_AXIOMS)
            self.assertEqual(len(audit["audit_source_sha256"]), 64)
            self.assertEqual(len(audit["report_sha256"]), 64)
            for text, diagnostic in probes:
                with self.subTest(diagnostic=diagnostic):
                    source.write_text(text)
                    (root / "validation.json").write_text('{"stale":"success"}')
                    with (patch.object(check, "ROOT", root),
                          patch.object(check, "command", side_effect=captured_command),
                          self.assertRaisesRegex(RuntimeError, "axiom audit failed")):
                        check.check_lean_proofs(MODEL_PROJECT, root, env, toolchain)
                    self.assertFalse((root / "validation.json").exists())
                    report = json.loads((root / "lean-proofs/axiom-audit.json").read_text())
                    self.assertEqual(report["status"], "fail")
                    self.assertIn(diagnostic, json.dumps(report["modules"]))

    def test_proof_library_rejects_false_theorems_and_placeholders(self):
        """Exercise the actual Lake proof gate, including imports and warning policy."""
        real_command = check.command

        def captured_command(args, **kwargs):
            # Exercise the mutant through Lake without rebuilding every proof root.
            if args == ["lake", "--no-cache", "build"]:
                args = [*args, "+GateProbe:olean"]
            return real_command(args, **dict(kwargs, capture=True, timeout=60))

        toolchain = (MODEL_PROJECT / "lean-toolchain").read_text().strip()
        env = dict(os.environ, ELAN_TOOLCHAIN=toolchain)
        probes = (
            ("theorem false_probe : (0 : Nat) = 1 := by rfl", "Tactic `rfl` failed"),
            ("theorem unfinished_probe : True := by sorry", "declaration uses `sorry`"),
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copytree(check.ROOT / "proofs", root / "proofs")
            for declaration, diagnostic in probes:
                with self.subTest(declaration=declaration):
                    (root / "validation.json").write_text('{"stale":"success"}')
                    (root / "proofs/GateProbe.lean").write_text(
                        "import Memory\n" + declaration + "\n"
                    )
                    with (
                        patch.object(check, "ROOT", root),
                        patch.object(check, "command", side_effect=captured_command),
                        self.assertRaises(subprocess.CalledProcessError) as failure,
                    ):
                        check.check_lean_proofs(MODEL_PROJECT, root, env, toolchain)
                    self.assertIn(diagnostic, failure.exception.stdout)
                    self.assertFalse((root / "validation.json").exists())


if __name__ == "__main__":
    unittest.main()
