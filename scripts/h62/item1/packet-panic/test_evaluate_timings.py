#!/usr/bin/env python3
"""Synthetic receipt controls only; these are not benchmark results."""
import copy
import hashlib
import json
import pathlib
import subprocess
import tempfile
import unittest

SCRIPT = pathlib.Path(__file__).with_name("evaluate_timings.py")
PIN = "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d"

class TimingGateTest(unittest.TestCase):
    def test_prerequisites_complete_groups_and_strict_threshold(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = pathlib.Path(tmp) / "synthetic.log"
            log.write_text("synthetic test fixture; not a timing receipt\n")
            receipt = {"status": "pass", "exit_code": 0, "log": str(log),
                       "sha256": hashlib.sha256(log.read_bytes()).hexdigest()}
            meta = {"base": "synthetic", "toolchain_sha256": PIN,
                    "lean_version": "Lean 4.35.0", "lake_version": "Lake Lean 4.35.0",
                    "threads": 1, "lean_args": ["-j1"], "memory_max_bytes": 12 * 1024**3,
                    "reserve_bytes": 4 * 1024**3, "swap_bytes": 0,
                    "cache_preparation": "synthetic", "resources": "synthetic"}
            old = {**receipt, "components_ns": {"original": 100}, "commands": {"original": "synthetic command"}}
            new = {**receipt, "components_ns": {"original": 109, "extracted_helper": 1}, "commands": {"original": "synthetic command", "extracted_helper": "synthetic helper"}}
            data = {"schema_version": 1, "original_components": ["original"],
                    "prerequisites": {k: receipt for k in ("toolchain", "keysort", "dependency", "helper", "equivalence", "axioms")},
                    "before": {"metadata": meta, "samples": [old]},
                    "after": {"metadata": copy.deepcopy(meta), "samples": [new]}}
            manifest = pathlib.Path(tmp) / "input.json"
            def run(value):
                manifest.write_text(json.dumps(value))
                result = subprocess.run(["python3", str(SCRIPT), str(manifest)], capture_output=True, text=True)
                return result.returncode, json.loads(result.stdout)
            code, result = run(data)
            self.assertEqual((code, result["status"]), (0, "declared_receipts_within_limit"))
            slow = copy.deepcopy(data)
            slow["after"]["samples"][0]["components_ns"]["original"] = 110
            code, result = run(slow)
            self.assertEqual((code, result["status"]), (1, "stop_slowdown"))
            for value in (None, [], "not an object", {"schema_version": True}):
                code, result = run(value)
                self.assertEqual((code, result["status"], result["delta_computed"]), (2, "invalid", False))
            malformed_version = copy.deepcopy(data)
            malformed_version["before"]["metadata"]["lean_version"] = ["4.35.0"]
            malformed_version["after"]["metadata"]["lean_version"] = ["4.35.0"]
            code, result = run(malformed_version)
            self.assertEqual((code, result["status"], result["delta_computed"]), (2, "invalid", False))
            for field in ("failed_prerequisite", "missing_helper", "different_conditions", "bad_log", "boolean_duration", "different_command", "malformed_samples", "malformed_receipt", "malformed_components"):
                bad = copy.deepcopy(data)
                if field == "failed_prerequisite":
                    bad["prerequisites"]["helper"]["status"] = "fail"
                elif field == "missing_helper":
                    del bad["after"]["samples"][0]["components_ns"]["extracted_helper"]
                elif field == "different_conditions":
                    bad["after"]["metadata"]["cache_preparation"] = "different"
                elif field == "bad_log":
                    bad["after"]["samples"][0]["sha256"] = "0" * 64
                elif field == "boolean_duration":
                    bad["before"]["samples"][0]["components_ns"]["original"] = True
                elif field == "different_command":
                    bad["after"]["samples"][0]["commands"]["original"] = "different command"
                elif field == "malformed_samples":
                    bad["after"]["samples"] = {"bad": "shape"}
                elif field == "malformed_receipt":
                    bad["before"]["samples"][0] = "not an object"
                else:
                    bad["after"]["samples"][0]["components_ns"] = [1, 2]
                code, result = run(bad)
                self.assertEqual((code, result["status"], result["delta_computed"]), (2, "invalid", False), field)

if __name__ == "__main__":
    unittest.main()
