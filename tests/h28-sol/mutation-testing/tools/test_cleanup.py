"""Fault-injected launcher failures only. No Lean proof success is mocked."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import Mock, patch
import bounded


class CleanupPriorityControls(unittest.TestCase):
    def invoke(self, cleanup, timeout_failure=False):
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "Probe.lean").write_text("-- Negative launcher fixture, never executed.\n")
            child = Mock()
            child.poll.return_value = None if timeout_failure else 0
            if timeout_failure:
                child.wait.side_effect = [subprocess.TimeoutExpired("docker", 1), OSError("wait failed")]
                child.kill.side_effect = OSError("kill failed")
            else:
                child.wait.return_value = 0
            def launch(argv, **kwargs):
                kwargs["stdout"].write(b"H28_MEASURE {not valid json}\n")
                return child
            state = {"State": {"OOMKilled": False}, "HostConfig": {"Memory": bounded.LIMIT, "MemorySwap": bounded.LIMIT, "NetworkMode": "none"}, "Mounts": []}
            inspect = subprocess.CompletedProcess([], 0, json.dumps([state]), "")
            with patch("bounded.headroom", return_value={"available_before": 16 * 1024**3, "memory_limit": bounded.LIMIT}), patch("bounded.subprocess.Popen", side_effect=launch), patch("bounded.subprocess.run", return_value=inspect), patch("bounded.remove_owned", return_value=cleanup) as remove:
                try:
                    return bounded.lean(tree, "Probe.lean", tree / "out.log", timeout=1)
                finally:
                    self.assertTrue(remove.called)
                    if timeout_failure: self.assertGreaterEqual(remove.call_count, 2)

    def test_uncertain_cleanup_overrides_malformed_measurement(self):
        with self.assertRaises(bounded.CleanupError) as context:
            self.invoke(False)
        self.assertFalse(context.exception.record["cleanup_confirmed"])
        self.assertEqual(context.exception.record["kind"], "error")

    def test_timeout_wait_failure_still_forces_cleanup_abort(self):
        with self.assertRaises(bounded.CleanupError):
            self.invoke(False, timeout_failure=True)

    def test_malformed_measurement_after_confirmed_cleanup_is_error(self):
        result = self.invoke(True)
        self.assertTrue(result["cleanup_confirmed"])
        self.assertEqual(result["kind"], "error")


if __name__ == "__main__": unittest.main(verbosity=2)
