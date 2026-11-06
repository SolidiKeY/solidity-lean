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


class LockAndClock(unittest.TestCase):
    def test_clock_disagreement_stops(self):
        import sys
        safe = {"memory_max": 12*guard.GIB, "memory_current": 1024,
                "swap_max": 0, "swap_current": 0, "available": 8*guard.GIB}
        with open("/dev/null", "w") as out, patch.object(guard, "sample", return_value=safe), patch.object(guard, "_clock_pair", side_effect=[(0, 0), (1, 2000000000)]):
            self.assertEqual("invalid-clock", guard.controlled_process([sys.executable, "-c", "import time; time.sleep(1)"], out, 2)["status"])

    def test_success_remains_untrusted_without_process_containment(self):
        lock_path = pathlib.Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
        if not lock_path.parent.is_dir():
            self.skipTest("writer lock directory unavailable")
        with open("/dev/null", "w") as out, patch.object(guard, "controlled_process", return_value={"status": "ok"}) as controlled:
            result = guard.locked_controlled_process(["ignored"], out)
            self.assertEqual("untrusted-prototype-success", result["status"])
            controlled.assert_called_once_with(["ignored"], out, timeout_seconds=300)

    def test_lock_refusal_does_not_spawn(self):
        import fcntl
        lock_path = pathlib.Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
        if not lock_path.parent.is_dir():
            self.skipTest("writer lock directory unavailable")
        with lock_path.open("a") as held, open("/dev/null", "w") as out:
            fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with patch.object(guard, "controlled_process") as controlled:
                self.assertEqual("lock-or-control-error", guard.locked_controlled_process(["ignored"], out)["status"])
                controlled.assert_not_called()


if __name__ == "__main__":
    unittest.main()
