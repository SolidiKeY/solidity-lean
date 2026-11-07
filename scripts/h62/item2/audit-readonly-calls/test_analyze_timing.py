#!/usr/bin/env python3
"""Mutation controls for offline timing evidence; no Lean or benchmark execution."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("timing", Path(__file__).with_name("analyze_timing.py"))
timing = importlib.util.module_from_spec(spec)
spec.loader.exec_module(timing)


class TimingEvidence(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.before = dict(command=["lean", "-j1", "fixture.lean"], file_sha256="same",
                           samples_seconds=[1, 1, 1, 1, 1], median_seconds=1)
        self.after = dict(self.before, samples_seconds=[1, 1, 2, 2, 2], median_seconds=2, delta_percent=100)
        self.write()

    def write(self):
        self.paths = []
        receipts = []
        for name, data in [("before", self.before), ("after", self.after)]:
            path = self.root/(name+".json")
            path.write_text(json.dumps(data))
            log = self.root/(name+".log")
            log.write_text(json.dumps(data)+("\nSLOWDOWN_STOP" if name == "after" else ""))
            receipt = {f: "same" for f in timing.IDENTITY_FIELDS}
            receipt.update(log=str(log), log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
                           command=["python3", "scripts/h62/item2/audit-readonly-calls/measure.py", "--output", str(path)] + (["--compare", str(self.root/"before.json")] if name == "after" else []),
                           stop_reason=None,
                           child_exit=0 if name == "before" else 1,
                           gate_exit=0 if name == "before" else 1,
                           status="pass" if name == "before" else "fail")
            rp=self.root/(name+"-receipt.json")
            rp.write_text(json.dumps(receipt))
            self.paths.append(path)
            receipts.append(rp)
        self.paths += receipts

    def check(self):
        return timing.analyze(*self.paths)

    def test_real_stop_preserved_without_causal_claim(self):
        result = self.check()
        self.assertEqual(result["recorded_timing_outcome"], "stop")
        self.assertEqual(result["cause"], "unestablished")
        self.assertEqual(result["after"]["first_two_median_seconds"], 1)
        self.assertEqual(result["after"]["last_three_median_seconds"], 2)

    def test_samples_detached_from_log_rejected(self):
        self.paths[1].write_text(json.dumps(self.before))
        with self.assertRaisesRegex(ValueError, "hash-bound log"):
            self.check()

    def test_altered_log_rejected(self):
        (self.root/"after.log").write_text("different")
        with self.assertRaisesRegex(ValueError, "log hash"):
            self.check()

    def test_forged_median_and_delta_rejected(self):
        for field in ("median_seconds", "delta_percent"):
            with self.subTest(field=field):
                original = copy.deepcopy(self.after)
                self.after[field] = 999
                self.write()
                with self.assertRaises(ValueError):
                    self.check()
                self.after = original

    def test_nonfinite_or_nonpositive_samples_rejected(self):
        for value in (float("inf"), float("nan"), 0, -1, True):
            with self.subTest(value=value):
                self.after["samples_seconds"][0] = value
                self.write()
                with self.assertRaises(ValueError):
                    self.check()

    def test_false_passing_receipt_rejected(self):
        p=self.paths[3]
        receipt=json.loads(p.read_text())
        receipt.update(child_exit=0, gate_exit=0, status="pass")
        p.write_text(json.dumps(receipt))
        with self.assertRaisesRegex(ValueError, "outcome disagrees"):
            self.check()

    def test_toolchain_mismatch_rejected(self):
        p=self.paths[3]
        receipt=json.loads(p.read_text());receipt["lean_binary_sha256"]="different"
        p.write_text(json.dumps(receipt))
        with self.assertRaisesRegex(ValueError, "identity mismatch"):
            self.check()

    def test_resource_guard_stop_rejected(self):
        for p in self.paths[2:]:
            with self.subTest(receipt=p.name):
                receipt=json.loads(p.read_text());receipt["stop_reason"]="memory cap/reserve guard"
                p.write_text(json.dumps(receipt))
                with self.assertRaisesRegex(ValueError, "resource guard stop"):
                    self.check()
                receipt["stop_reason"]=None;p.write_text(json.dumps(receipt))

    def test_unrelated_command_or_baseline_rebinding_rejected(self):
        for index in (2, 3):
            with self.subTest(receipt=index):
                p=self.paths[index];original=json.loads(p.read_text());receipt=copy.deepcopy(original)
                receipt["command"][0]="unrelated-producer";p.write_text(json.dumps(receipt))
                with self.assertRaisesRegex(ValueError, "noncanonical"):
                    self.check()
                p.write_text(json.dumps(original))
        p=self.paths[3];receipt=json.loads(p.read_text());receipt["command"][-1]="different-baseline"
        p.write_text(json.dumps(receipt))
        with self.assertRaisesRegex(ValueError, "baseline binding"):
            self.check()


if __name__ == "__main__":
    unittest.main()
