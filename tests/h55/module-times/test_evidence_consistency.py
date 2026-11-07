import copy
import importlib.util
import pathlib
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/evidence_consistency.py"
spec = importlib.util.spec_from_file_location("consistency", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class Consistency(unittest.TestCase):
    def setUp(self):
        self.inventory = [{"path": "Solidity/A.lean", "sha256": "a" * 64}]
        self.binding = {"head": "b" * 40, "tool_sha256": "c" * 64, "cache_sha256": "d" * 64,
                        "image_sha256": "e" * 64, "vm_identity": "fixture", "lean_version": "fixture", "lake_version": "fixture"}
        self.row = {**self.binding, "path": "Solidity/A.lean", "source_sha256": "a" * 64,
                    "cache_after_sha256": "d" * 64, "status": "ok", "exit_code": 0, "fresh": True,
                    "lean_jobs": 1, "lean_threads": 1, "resources": {"memory_max": 12 * module.GIB,
                    "swap_max": 0, "minimum_available": 4 * module.GIB}, "peak_rss_kib": 100,
                    "mono_start_ns": 10, "mono_end_ns": 1000000010,
                    "boot_start_ns": 20, "boot_end_ns": 1000000020, "wall_seconds": 1.0}

    def test_complete_and_missing_duplicate(self):
        self.assertEqual([], module.validate(self.inventory, self.binding, [self.row]))
        self.assertTrue(module.validate(self.inventory, self.binding, []))
        self.assertTrue(module.validate(self.inventory, self.binding, [self.row, self.row]))
        self.assertTrue(module.validate(self.inventory, {}, [self.row]))

    def test_recorded_intervals_must_be_serial(self):
        inventory = self.inventory + [{"path": "Solidity/B.lean", "sha256": "f" * 64}]
        other = {**self.row, "path": "Solidity/B.lean", "source_sha256": "f" * 64}
        self.assertTrue(module.validate(inventory, self.binding, [self.row, other]))
        other.update(mono_start_ns=1000000010, mono_end_ns=2000000010,
                     boot_start_ns=1000000020, boot_end_ns=2000000020)
        self.assertEqual([], module.validate(inventory, self.binding, [other, self.row]))
        other.update(boot_start_ns=500000020, boot_end_ns=1500000020)
        self.assertTrue(module.validate(inventory, self.binding, [self.row, other]))

    def test_unsafe_path_and_extreme_clock_rejected(self):
        inventory = [{"path": "../A.lean", "sha256": "a" * 64}]
        self.assertTrue(module.validate(inventory, self.binding, [self.row]))
        row = {**self.row, "mono_end_ns": 10 ** 500}
        self.assertTrue(module.validate(self.inventory, self.binding, [row]))

    def test_failed_measurements_are_not_passes(self):
        changes = [("status", "timeout"), ("exit_code", True), ("fresh", False), ("lean_jobs", 2),
                   ("lean_threads", True), ("source_sha256", "f" * 64), ("tool_sha256", "f" * 64),
                   ("cache_after_sha256", "f" * 64), ("wall_seconds", float("nan")),
                   ("wall_seconds", 301), ("boot_end_ns", 3000000020), ("peak_rss_kib", 0)]
        for key, value in changes:
            row = copy.deepcopy(self.row)
            row[key] = value
            with self.subTest(key=key, value=value):
                self.assertTrue(module.validate(self.inventory, self.binding, [row]))
        for key, value in [("swap_max", 1), ("memory_max", 13 * module.GIB), ("minimum_available", 4 * module.GIB - 1)]:
            row = copy.deepcopy(self.row)
            row["resources"][key] = value
            with self.subTest(key=key, value=value):
                self.assertTrue(module.validate(self.inventory, self.binding, [row]))


if __name__ == "__main__":
    unittest.main()
