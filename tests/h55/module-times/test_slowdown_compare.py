import copy
import json
import subprocess
import sys
import tempfile
import importlib.util
import pathlib
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/slowdown_compare.py"
spec = importlib.util.spec_from_file_location("slowdown_compare", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class Slowdown(unittest.TestCase):
    def setUp(self):
        env = {"vm_identity": "fixture", "cpu": "fixture", "lean_version": "fixture", "lake_version": "fixture",
               "tool_sha256": "a" * 64, "cache_sha256": "b" * 64, "image_sha256": "c" * 64,
               "unchanged_inputs_sha256": "d" * 64, "memory_max": 12 * module.GIB, "swap_max": 0, "threads": 1, "jobs": 1}
        self.before = {"path": "Solidity/A.lean", "head": "e" * 40, "source_sha256": "f" * 64,
                       "environment": env, "status": "ok", "exit_code": 0, "fresh": True,
                       "wall_ns": 100, "peak_rss_kib": 1000, "minimum_available": 4 * module.GIB}
        self.after = copy.deepcopy(self.before)
        self.after.update(head="1" * 40, source_sha256="2" * 64, wall_ns=110)

    def test_exact_threshold_and_stop(self):
        self.assertEqual("within-bound", module.compare(self.before, self.after)["verdict"])
        self.after["wall_ns"] = 111
        self.assertEqual("stop-slowdown", module.compare(self.before, self.after)["verdict"])

    def test_full_expected_set_and_stop_precedence(self):
        paths = ["Solidity/A.lean", "Solidity/B.lean"]
        before_b = copy.deepcopy(self.before)
        after_b = copy.deepcopy(self.after)
        before_b["path"] = after_b["path"] = paths[1]
        result = module.compare_all(paths, [before_b, self.before], [self.after, after_b])
        self.assertEqual("within-bound", result["verdict"])
        self.assertEqual("invalid", module.compare_all(paths, [self.before], [self.after, after_b])["verdict"])
        self.assertEqual("invalid", module.compare_all(paths, [self.before, self.before], [self.after, after_b])["verdict"])
        after_b["wall_ns"] = 111
        result = module.compare_all(paths, [self.before, before_b], [after_b])
        self.assertEqual("stop-slowdown", result["verdict"])
        self.assertEqual([paths[1]], result["slowdowns"])
        self.assertTrue(result["errors"])
        duplicate_slow = copy.deepcopy(self.after)
        duplicate_slow["wall_ns"] = 111
        result = module.compare_all([paths[0]], [self.before], [self.after, duplicate_slow])
        self.assertEqual("stop-slowdown", result["verdict"])
        self.assertTrue(result["errors"])

    def test_cli_checks_expected_set(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = pathlib.Path(tmp) / "input.json"
            payload.write_text(json.dumps({"expected_paths": ["Solidity/A.lean", "Solidity/B.lean"],
                                           "before": [self.before], "after": [self.after]}))
            process = subprocess.run([sys.executable, str(path), str(payload)], capture_output=True, text=True)
            self.assertNotEqual(0, process.returncode)
            self.assertEqual("invalid", json.loads(process.stdout)["verdict"])

    def test_over_budget_measurements_are_invalid(self):
        before = copy.deepcopy(self.before)
        after = copy.deepcopy(self.after)
        before["wall_ns"] = after["wall_ns"] = 300_000_000_001
        self.assertEqual("invalid", module.compare(before, after)["verdict"])

    def test_failures_and_unmatched_conditions_never_pass(self):
        for key, value in [("path", "../A.lean"), ("status", "timeout"), ("exit_code", True),
                           ("fresh", False), ("wall_ns", 0), ("wall_ns", True),
                           ("peak_rss_kib", 0), ("minimum_available", 4 * module.GIB - 1)]:
            row = copy.deepcopy(self.after)
            row[key] = value
            with self.subTest(key=key, value=value):
                self.assertEqual("invalid", module.compare(self.before, row)["verdict"])
        for key, value in [("cache_sha256", "3" * 64), ("unchanged_inputs_sha256", "4" * 64),
                           ("threads", 2), ("swap_max", 1), ("cpu", "other")]:
            row = copy.deepcopy(self.after)
            row["environment"][key] = value
            with self.subTest(key=key, value=value):
                self.assertEqual("invalid", module.compare(self.before, row)["verdict"])


if __name__ == "__main__":
    unittest.main()
