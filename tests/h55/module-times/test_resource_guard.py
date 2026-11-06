import importlib.util
import pathlib
import unittest
from unittest.mock import patch

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/resource_guard.py"
spec = importlib.util.spec_from_file_location("resource_guard", path)
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)


class Resources(unittest.TestCase):
    def test_enforced_boundaries(self):
        good = {"memory_max": 12*guard.GIB, "memory_current": 8*guard.GIB,
                "swap_max": 0, "swap_current": 0, "available": 4*guard.GIB}
        self.assertEqual([], guard.validate(good))
        for key, value in [("memory_max", 12*guard.GIB+1), ("memory_max", -1),
                           ("memory_current", 8*guard.GIB+1), ("swap_max", 1),
                           ("swap_current", 1), ("available", 4*guard.GIB-1),
                           ("available", True), ("available", None)]:
            with self.subTest(key=key, value=value):
                self.assertTrue(guard.validate({**good, key: value}))
        self.assertTrue(guard.validate({}))
        with patch.object(guard, "sample", side_effect=ValueError("unknown")):
            self.assertTrue(guard.preflight())


if __name__ == "__main__":
    unittest.main()

class MonitoredControls(unittest.TestCase):
    def test_success_failure_timeout_and_resource_stop(self):
        import subprocess
        import sys
        safe = {"memory_max": 12*guard.GIB, "memory_current": 1024,
                "swap_max": 0, "swap_current": 0, "available": 8*guard.GIB}
        with open("/dev/null", "w") as out, patch.object(guard, "sample", return_value=safe):
            self.assertEqual("ok", guard.controlled_process([sys.executable, "-c", "pass"], out, 2)["status"])
            self.assertEqual("failed", guard.controlled_process([sys.executable, "-c", "raise SystemExit(2)"], out, 2)["status"])
            self.assertEqual("timeout-or-invalid-clock", guard.controlled_process([sys.executable, "-c", "import time; time.sleep(2)"], out, .05)["status"])
            self.assertEqual("spawn-error", guard.controlled_process(["/nonexistent/h55-command"], out, 2)["status"])
        with open("/dev/null", "w") as out, patch.object(guard, "sample", side_effect=[safe, {**safe, "available": 0}]):
            self.assertEqual("resource-stop", guard.controlled_process([sys.executable, "-c", "import time; time.sleep(2)"], out, 2)["status"])
        with open("/dev/null", "w") as out, patch.object(guard, "sample", side_effect=ValueError("unavailable")), patch.object(subprocess, "Popen") as spawn:
            self.assertEqual("resource-stop", guard.controlled_process([sys.executable, "-c", "pass"], out)["status"])
            spawn.assert_not_called()

    def test_rejects_invalid_limits(self):
        for limit in [0, 301, True, float("nan")]:
            with self.subTest(limit=limit), self.assertRaises(ValueError):
                guard.controlled_process(["x"], None, limit)
