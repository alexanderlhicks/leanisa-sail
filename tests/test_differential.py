"""Acceptance controls for three independent target results and bounded replay."""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("differential", ROOT / "scripts/differential.py")
d = importlib.util.module_from_spec(spec)
spec.loader.exec_module(d)


def field(n):
    return {"status": "ok", "answer": {"base": f"{n & d.MASK:016x}", "extension": d.word(n)}}


def image(verdict, **fields):
    return {"status": "ok", "answer": {"verdict": verdict, **fields}}


class DifferentialAcceptance(unittest.TestCase):
    def test_two_identical_wrong_targets_do_not_hide_rust_difference(self):
        for limb in (0, 64, 128):
            with self.assertRaisesRegex(RuntimeError, "semantic mismatch"):
                d.compare_primitive([field(1 << limb), field(0), field(1 << limb)], "field")

    def test_missing_and_malformed_target_never_pass(self):
        for bad in ({"status": "timeout"}, {"status": "panic"}, {"status": "ok", "answer": {"base": "0", "extension": d.word(0)}}):
            with self.assertRaises(RuntimeError):
                d.compare_primitive([field(0), field(0), bad], "field")

    def test_codec_omission_rejected_even_if_three_targets_agree(self):
        req = {"kind": "codec", "program": [["xor", 0, 0, 0], ["mul", 0, 0, 0]]}
        reply = {"status": "ok", "answer": {"encoding": [["0000000000000000"] * 8]}}
        with self.assertRaisesRegex(RuntimeError, "row count"):
            d.validate_reply_request(reply, req)

    def test_every_encoding_column_is_compared(self):
        for column in range(8):
            correct = {"status": "ok", "answer": {"encoding": [["0000000000000000"] * 8]}}
            wrong = json.loads(json.dumps(correct))
            wrong["answer"]["encoding"][0][column] = "0000000000000001"
            with self.assertRaisesRegex(RuntimeError, "semantic mismatch"):
                d.compare_primitive([wrong, correct, wrong], "codec")

    def test_raw_blake_flags_and_all_digest_limbs_are_preserved(self):
        req = {"kind": "blake", "message": ["0000000000000000"] * 8,
               "cv": ["0000000000000000"] * 4, "md": d.word(0x123456789ABCDEF0 << 64)}
        d.validate_request(req)
        self.assertIn("123456789abcdef0", d.sail_source([req]))
        for limb in range(4):
            correct = {"status": "ok", "answer": ["0000000000000000"] * 4}
            wrong = json.loads(json.dumps(correct))
            wrong["answer"][limb] = "0000000000000001"
            with self.assertRaisesRegex(RuntimeError, "semantic mismatch"):
                d.compare_primitive([correct, wrong, correct], "blake")

    def test_rejection_mapping_keeps_fuel_and_success_distinct(self):
        for error in ("BadAccess", "BadValue", "BadInstance"):
            d.compare_image(image(error), image("Rejected", error="invalidStep"), error)
        for verdict in ("Halted", "OutOfFuel"):
            with self.assertRaises(RuntimeError):
                d.compare_image(image(verdict), image("Rejected"), verdict)
        with self.assertRaises(RuntimeError):
            d.compare_image(image("OutOfFuel"), image("Halted"), "OutOfFuel")

    def test_halted_register_count_omissions_are_rejected(self):
        sail = image("Halted", pc="0000000000000002", fp="0000000000000001", expected_steps=1)
        good = image("Halted", pc="0000000000000002", fp="0000000000000001", steps=1)
        d.compare_image(sail, good, "Halted")
        for missing in ("pc", "fp", "steps"):
            bad = json.loads(json.dumps(good))
            del bad["answer"][missing]
            with self.assertRaises(RuntimeError):
                d.compare_image(sail, bad, "Halted")
        bad = json.loads(json.dumps(good))
        bad["answer"]["steps"] = 2
        with self.assertRaises(RuntimeError):
            d.compare_image(sail, bad, "Halted")

    def test_rust_image_produces_fuel_public_and_instruction_mutations(self):
        case = {"name": "fixture", "expected_verdict": "Halted", "corrupt_cell": 2,
                "request": {"kind": "execute", "program": [["set", 2, d.word(7)], ["xor", 0, 0, 0]], "input": [d.word(0)] * 2}}
        answer = {"memory_size": 65536, "cells": [[2, d.word(7)]], "cycles": 1,
                  "main_cycles": 1, "base_counts": [0, 0, 1, 0, 0, 0],
                  "encoding": [["0000000000000000"] * 8] * 2, "unconstrained_reads": []}
        variants = d.image_cases(case, answer)
        expected = {"fixture-exact": "Halted", "fixture-zero": "OutOfFuel", "fixture-insufficient": "OutOfFuel",
                    "fixture-surplus": "Halted", "fixture-public-corruption": "BadInstance", "fixture-mutation-0": "BadValue"}
        self.assertEqual({name: verdict for name, _, verdict in variants}, expected)
        self.assertEqual([req["fuel"] for _, req, _ in variants[:4]], [1, 0, 0, 2])
        self.assertEqual(variants[-1][1]["cells"], [[2, d.word(6)]])
        for _, req, _ in variants:
            d.validate_request(req)

    def test_exact_maximum_fuel_does_not_create_out_of_profile_surplus(self):
        case = {"name": "cap", "expected_verdict": "Halted",
                "request": {"kind": "execute", "program": [["xor", 0, 0, 0]] * 2, "input": [d.word(0)] * 2}}
        answer = {"memory_size": 65536, "cells": [], "cycles": 1024, "main_cycles": 1024,
                  "base_counts": [1024, 0, 0, 0, 0, 0], "encoding": [["0000000000000000"] * 8] * 2, "unconstrained_reads": []}
        variants = d.image_cases(case, answer)
        self.assertFalse(any(name.endswith("surplus") for name, _, _ in variants))
        for _, req, _ in variants:
            d.validate_request(req)

    def test_process_failures_are_not_semantic_rejections(self):
        descriptor = lambda code: {"command": [sys.executable, "-c", code]}
        req = {"kind": "field", "a": d.word(0), "b": d.word(0)}
        self.assertEqual(d.adapter_batch(descriptor("import time; time.sleep(10)"), [req], .1)[0]["status"], "timeout")
        self.assertEqual(d.adapter_batch(descriptor("raise SystemExit(3)"), [req], 2)[0]["status"], "crash")
        self.assertEqual(d.adapter_batch(descriptor("print('{}')"), [req], 2)[0]["status"], "protocol_error")
        self.assertEqual(d.adapter_batch(descriptor("print('{\"status\":\"ok\",\"status\":\"rejected\"}')"), [req], 2)[0]["status"], "protocol_error")

    def test_output_limit_interrupts_a_running_process(self):
        result = d.process([sys.executable, "-c", "import sys,time; sys.stdout.write('x'*65536); sys.stdout.flush(); time.sleep(10)"],
                           timeout=2, output_limit=1024)
        self.assertEqual(result["status"], "output_limit")

    def test_successful_leader_cannot_leave_a_live_descendant(self):
        code = "import subprocess,sys; p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL); print(p.pid)"
        result = d.process([sys.executable, "-c", code], timeout=2)
        self.assertEqual(result["status"], "ok")
        pid = int(result["stdout"].strip())
        for _ in range(50):
            status = Path(f"/proc/{pid}/stat")
            if not status.exists() or status.read_text().split()[2] == "Z":
                break
            time.sleep(.02)
        else:
            os.kill(pid, 9)
            self.fail("descendant survived its completed process group")

    def test_wrong_sail_compiler_commit_is_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "Sail executable"):
            d.validate_sail_version("Sail 0.20.2 (sail2 @ wrong)", "ce60ba570b4402a42431bc5033145d9aeb327f20")

    def test_minimizer_cannot_replace_codec_mismatch_with_row_count_error(self):
        req = {"kind": "codec", "program": [["xor", 0, 0, 0]] * 2}
        correct = {"status": "ok", "answer": {"encoding": [["0000000000000000"] * 8] * 2}}
        wrong = json.loads(json.dumps(correct))
        wrong["answer"]["encoding"][1][0] = "0000000000000001"
        observed = {"sail": wrong, "leanvm": correct, "leanervm": wrong}
        def evaluate(candidate, label):
            return observed, "codec response row count differs from request"
        case = {"name": "codec", "request": req}
        reduced, _, attempts = d.minimize_case(case, observed, evaluate, 4)
        self.assertEqual(reduced, case)
        self.assertEqual(attempts, 2)

    def test_image_reduction_cannot_change_semantic_error_class(self):
        a = {"sail": image("BadValue"), "leanervm": image("Rejected")}
        b = {"sail": image("BadAccess"), "leanervm": image("Rejected")}
        self.assertNotEqual(d.failure_signature(a, "image"), d.failure_signature(b, "image"))

    def test_power_of_two_common_profile_applies_to_codec_replay(self):
        with self.assertRaisesRegex(RuntimeError, "power of two"):
            d.validate_request({"kind": "codec", "program": [["xor", 0, 0, 0]] * 3})

    def test_saved_failure_replay_survives_cleanup(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            failure = build / "failure.json"
            content = '{"case":{"name":"failure"}}'
            failure.write_text(content)
            (build / "report.json").write_text('{"status":"pass"}')
            self.assertEqual(d.fresh_outputs(build, failure), content)
            self.assertFalse(failure.exists())
            self.assertFalse((build / "report.json").exists())

    def test_saved_halt_count_failure_is_checked_again_on_replay(self):
        case = {"name": "count", "expected_verdict": "Halted", "expected_main_cycles": 1}
        sail = image("Halted", pc="0000000000000002", fp="0000000000000001")
        lean = image("Halted", pc="0000000000000002", fp="0000000000000001", steps=2)
        d.attach_expected_count(case, sail)
        with self.assertRaisesRegex(RuntimeError, "main step count mismatch"):
            d.compare_image(sail, lean, case["expected_verdict"])

    def test_minimization_keeps_target_relation_and_rejects_crash(self):
        case = {"name": "fail", "request": {"kind": "field", "a": d.word(7), "b": d.word(3)}}
        observed = {"sail": field(0), "leanvm": field(1), "leanervm": field(0)}
        calls = []
        def evaluate(candidate, label):
            calls.append(candidate)
            if d.integer(candidate["request"]["a"]) == 0:
                return {"sail": field(0), "leanvm": {"status": "panic"}, "leanervm": field(0)}, "panic"
            return observed, "semantic mismatch"
        reduced, replies, attempts = d.minimize_case(case, observed, evaluate, 10)
        self.assertGreater(attempts, 0)
        self.assertLessEqual(attempts, 10)
        self.assertNotEqual(d.integer(reduced["request"]["a"]), 0)
        self.assertEqual(d.failure_signature(replies, "field"), d.failure_signature(observed, "field"))

    def test_previous_success_is_removed_when_startup_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            report = build / "report.json"
            report.write_text('{"status":"pass"}')
            result = subprocess.run([sys.executable, "-O", ROOT / "scripts/differential.py", "--sail-root", build / "absent",
                                     "--leanvm", build / "absent", "--leanervm", build / "absent", "--build", build], capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)
            self.assertFalse(report.exists())
            self.assertEqual(json.loads((build / "failure.json").read_text())["status"], "startup_or_campaign_failure")

    def test_invalid_numeric_options_remove_previous_success(self):
        for option in (['--cases', '-1'], ['--timeout', 'nan'], ['--minimize', '65']):
            with tempfile.TemporaryDirectory() as tmp:
                build = Path(tmp)
                report = build / "report.json"
                report.write_text('{"status":"pass"}')
                result = subprocess.run([sys.executable, "-O", ROOT / "scripts/differential.py", "--sail-root", build,
                                         "--leanvm", build, "--leanervm", build, "--build", build, *option], capture_output=True, text=True)
                self.assertEqual(result.returncode, 1)
                self.assertFalse(report.exists())


if __name__ == "__main__":
    unittest.main()
