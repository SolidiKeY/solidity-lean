import importlib.util
import pathlib
import sys
import unittest
from unittest.mock import patch

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/measurement_control.py"
spec = importlib.util.spec_from_file_location("measurement_control", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class MeasurementControls(unittest.TestCase):
    def test_real_success_failure_timeout_spawn(self):
        self.assertEqual("ok", module.run_control([sys.executable, "-c", "pass"], 2)["status"])
        self.assertEqual("failed", module.run_control([sys.executable, "-c", "raise SystemExit(7)"], 2)["status"])
        self.assertEqual("timeout", module.run_control([sys.executable, "-c", "import time; time.sleep(2)"], .05)["status"])
        self.assertEqual("spawn-error", module.run_control(["/nonexistent/h55-command"], 2)["status"])

    def test_fake_clock_disagreement_and_invalid_times(self):
        self.assertEqual(1, module.check_clocks((1, 1), (1000000001, 1000000001), 2))
        for start, end in [((1, 1), (1, 1)), ((2, 2), (1, 1)),
                           ((0, 0), (1, 2000000000)), ((0, 0), (3000000000, 3000000000)),
                           ((True, 0), (1, 1))]:
            with self.subTest(start=start, end=end):
                self.assertIsNone(module.check_clocks(start, end, 2))
        with patch.object(module, "clocks", side_effect=[(0, 0), (1, 2000000000)]):
            self.assertEqual("invalid-clock-or-over-budget", module.run_control([sys.executable, "-c", "pass"], 2)["status"])

    def test_invalid_configuration(self):
        for argv, timeout in [([], 1), (["x"], 0), (["x"], float("nan")), (["x"], True), ([""], 1)]:
            with self.subTest(argv=argv, timeout=timeout), self.assertRaises(ValueError):
                module.run_control(argv, timeout)


if __name__ == "__main__":
    unittest.main()
