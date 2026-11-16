#!/usr/bin/env python3
"""Behavioral guard regressions: refusal, isolation and monitoring failure."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import bounded


def good():
    return dict(limit=16*1024**3, current=1024**3, working=1024**3,
                effective_free=15*1024**3, os_available=15*1024**3)


class GuardTests(unittest.TestCase):
    def test_process_limit_is_enforced_without_resident_allocation(self):
        code = """import mmap,resource,sys
assert resource.getrlimit(resource.RLIMIT_AS)[0] <= 12*1024**3
try:
    value=mmap.mmap(-1,13*1024**3)
except (OSError,MemoryError,OverflowError):
    sys.exit(0)
value.close()
sys.exit(1)
"""
        result = bounded.run([sys.executable, "-c", code], sampler=good)
        self.assertEqual(result["exit"], 0)
        self.assertFalse(result["resource_stop"])

    def test_effective_reserve_refuses_before_start(self):
        with tempfile.TemporaryDirectory() as temp:
            marker = Path(temp) / "started"
            def low():
                sample = good()
                sample["effective_free"] = bounded.RESERVE-1
                return sample
            command = [sys.executable, "-c", "from pathlib import Path; Path(" + repr(str(marker)) + ").touch()"]
            result = bounded.run(command, sampler=low)
            self.assertEqual(result["exit"], 125)
            self.assertIsNone(result["child_exit"])
            self.assertFalse(marker.exists())

    def test_os_reserve_refuses_before_start(self):
        def low():
            sample = good()
            sample["os_available"] = bounded.RESERVE-1
            return sample
        result = bounded.run([sys.executable, "-c", "raise AssertionError('must not run')"], sampler=low)
        self.assertEqual(result["exit"], 125)
        self.assertIsNone(result["child_exit"])

    def test_sampler_exception_terminates_child_but_not_other_invocation(self):
        sentinel = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"],
                                    start_new_session=True,
                                    env=dict(os.environ, TVYUL_RESOURCE_TAG="tv-yul-prototype-1108"))
        calls = 0
        def faulty():
            nonlocal calls
            calls += 1
            if calls > 1:
                raise OSError("injected sampling read failure")
            return good()
        try:
            result = bounded.run([sys.executable, "-c", "import time; time.sleep(30)"],
                                 sampler=faulty, interval=0.02)
            self.assertEqual(result["exit"], 125)
            self.assertTrue(result["resource_stop"])
            self.assertIn("injected sampling read failure", result["monitor_error"])
            self.assertEqual(result["child_exit"], -9)
            self.assertLess(result["seconds"], 5)
            self.assertIsNone(sentinel.poll())
        finally:
            sentinel.terminate()
            sentinel.wait()

    def test_final_sample_failure_cannot_turn_into_success(self):
        calls = 0
        def faulty():
            nonlocal calls
            calls += 1
            if calls > 1:
                raise ValueError("invalid resource counter")
            return good()
        result = bounded.run([sys.executable, "-c", "pass"], sampler=faulty, interval=10)
        self.assertEqual(result["child_exit"], 0)
        self.assertEqual(result["exit"], 125)
        self.assertTrue(result["resource_stop"])
        self.assertIn("invalid resource counter", result["monitor_error"])

    def test_initial_sampling_failure_does_not_spawn(self):
        def faulty():
            raise FileNotFoundError("missing cgroup counters")
        result = bounded.run([sys.executable, "-c", "raise AssertionError('must not run')"], sampler=faulty)
        self.assertEqual(result["exit"], 125)
        self.assertIsNone(result["child_exit"])

    def test_lower_inherited_cap_is_preserved_and_reported(self):
        code = """import json,resource,sys,bounded
resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3))
from test_bounded import good
result=bounded.run([sys.executable,'-c','import resource; assert resource.getrlimit(resource.RLIMIT_AS)[0] == 8*1024**3'],sampler=good)
print(json.dumps(result))
"""
        child = subprocess.run([sys.executable, "-B", "-c", code],
                               cwd=Path(bounded.__file__).parent, capture_output=True, text=True)
        self.assertEqual(child.returncode, 0, child.stderr)
        result = json.loads(child.stdout)
        self.assertEqual(result["exit"], 0)
        self.assertEqual(result["applied_process_address_space_limit"], 8*1024**3)

    def test_pidfd_monitoring_error_refuses_and_reaps(self):
        with patch("bounded.select.select", side_effect=OSError("injected pidfd error")):
            result = bounded.run([sys.executable, "-c", "import time; time.sleep(30)"], sampler=good)
        self.assertEqual(result["exit"], 125)
        self.assertEqual(result["child_exit"], -9)
        self.assertIn("injected pidfd error", result["monitor_error"])

    def test_removed_vm_cap_bypass_is_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            record = Path(temp) / "result.json"
            command = [sys.executable, "-B", bounded.__file__, str(record), sys.executable, "-c", "pass"]
            child = subprocess.run(command, env=dict(os.environ, TVYUL_USE_VM_CAP="1"),
                                   capture_output=True, text=True)
            self.assertEqual(child.returncode, 125)
            result = json.loads(record.read_text())
            self.assertTrue(result["resource_stop"])
            self.assertIn("removed", result["monitor_error"])


if __name__ == "__main__":
    unittest.main()
