import importlib.util
import pathlib
import subprocess
import unittest
from unittest.mock import patch

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/container_watch.py"
spec = importlib.util.spec_from_file_location("container_watch", path)
watch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(watch)


class WatchControls(unittest.TestCase):
    container = "a" * 64
    nonce = "b" * 32

    def test_ownership_mismatch_never_kills(self):
        with patch.object(watch, "docker", return_value="other|true|0|67108864|67108864|none|16|123") as docker:
            with self.assertRaises(ValueError):
                watch.stop_owned(self.container, self.nonce)
            self.assertEqual(1, docker.call_count)
            self.assertEqual("inspect", docker.call_args.args[0])

    def test_resource_policy_mismatch_rejected(self):
        for payload in ["b" * 32 + "|true|0|0|0|none|16|123",
                        "b" * 32 + "|true|0|67108864|134217728|none|16|123",
                        "b" * 32 + "|true|0|67108864|67108864|bridge|16|123",
                        "b" * 32 + "|true|0|67108864|67108864|none|0|123"]:
            with self.subTest(payload=payload), patch.object(watch, "docker", return_value=payload):
                with self.assertRaises(ValueError):
                    watch.state(self.container, self.nonce)
                self.assertEqual((True, 0), watch.state(self.container, self.nonce, check_limits=False))

    def test_effective_limit_failure_cannot_pass(self):
        payload = self.nonce + "|true|0|67108864|67108864|none|16|123"
        with patch.object(watch, "docker", return_value=payload), \
             patch.object(watch, "kernel_limits", side_effect=ValueError("kernel mismatch")):
            with self.assertRaises(ValueError):
                watch.state(self.container, self.nonce)
            self.assertEqual((True, 0), watch.state(self.container, self.nonce, check_limits=False))

    def test_start_delay_counts_against_deadline(self):
        """Guard regression: time spent in Docker start is omitted."""
        def daemon(*args, **kwargs):
            if args[0] == "inspect":
                return self.nonce + "|created"
            self.assertEqual("start", args[0])
            return self.container
        with patch.object(watch, "docker", side_effect=daemon), \
             patch.object(watch, "host_headroom", return_value=True), \
             patch.object(watch.time, "monotonic_ns", side_effect=[0, 350_000_000]), \
             patch.object(watch.time, "clock_gettime_ns", side_effect=[0, 350_000_000]), \
             patch.object(watch, "stop_owned", return_value=137):
            self.assertEqual({"status": "timeout", "exit_code": 137},
                             watch.start_and_watch(self.container, self.nonce, .3))

    def test_prestarted_or_unavailable_container_is_not_launched(self):
        """Guard regression: an existing run is relabeled as freshly started."""
        with patch.object(watch, "docker", return_value=self.nonce + "|running") as daemon:
            result = watch.start_and_watch(self.container, self.nonce, 1)
            self.assertEqual("untrusted-prestart-state", result["status"])
            self.assertEqual(1, daemon.call_count)
        with patch.object(watch, "docker", return_value=self.nonce + "|created") as daemon, \
             patch.object(watch, "host_headroom", return_value=False):
            self.assertEqual("resource-stop-before-start", watch.start_and_watch(self.container, self.nonce, 1)["status"])
            self.assertEqual(1, daemon.call_count)

    def test_start_uses_unchanged_full_budget(self):
        """Guard regression: an unapproved one-second start budget is imposed."""
        def daemon(*args, **kwargs):
            if args[0] == "inspect":
                return self.nonce + "|created"
            self.assertEqual(300, kwargs["timeout"])
            return self.container
        with patch.object(watch, "docker", side_effect=daemon), \
             patch.object(watch, "host_headroom", return_value=True), \
             patch.object(watch, "watch", return_value={"status": "unobserved-exit", "exit_code": 0}):
            self.assertEqual("unobserved-exit", watch.start_and_watch(self.container, self.nonce)["status"])

    def test_failed_start_does_not_claim_cleanup_or_pass(self):
        """Guard regression: a timed-out start is accepted as cleaned up."""
        def daemon(*args, **kwargs):
            if args[0] == "inspect":
                return self.nonce + "|created"
            raise subprocess.TimeoutExpired("docker", 1)
        with patch.object(watch, "docker", side_effect=daemon), \
             patch.object(watch, "host_headroom", return_value=True), \
             patch.object(watch, "stop_owned", return_value=137):
            self.assertEqual("untrusted-start-error", watch.start_and_watch(self.container, self.nonce, 1)["status"])

    def test_bad_inputs_refused_without_docker(self):
        with patch.object(watch, "docker") as docker:
            for cid, nonce, seconds in [("wrong", self.nonce, 1), (self.container, "bad", 1),
                                        (self.container, self.nonce, 301), (self.container, self.nonce, float("nan"))]:
                with self.subTest(seconds=seconds), self.assertRaises(ValueError):
                    watch.watch(cid, nonce, seconds)
            docker.assert_not_called()

    def test_disagreeing_clocks_stop_owned_container(self):
        with patch.object(watch, "host_headroom", return_value=True), \
             patch.object(watch.time, "monotonic_ns", side_effect=[0, 1]), \
             patch.object(watch.time, "clock_gettime_ns", side_effect=[0, 2_000_000_000]), \
             patch.object(watch, "stop_owned", return_value=137) as stop:
            self.assertEqual({"status": "invalid-clock", "exit_code": 137}, watch.watch(self.container, self.nonce, 2))
            stop.assert_called_once_with(self.container, self.nonce)

    def test_inspection_timeout_after_deadline_is_classified(self):
        with patch.object(watch, "host_headroom", return_value=True), \
             patch.object(watch.time, "monotonic_ns", side_effect=[0, 100_000_000, 350_000_000]), \
             patch.object(watch.time, "clock_gettime_ns", side_effect=[0, 100_000_000, 350_000_000]), \
             patch.object(watch, "state", side_effect=subprocess.TimeoutExpired("docker", .2)), \
             patch.object(watch, "stop_owned", return_value=137):
            self.assertEqual({"status": "timeout", "exit_code": 137}, watch.watch(self.container, self.nonce, .3))

    def test_slow_exit_inspection_does_not_bypass_deadline(self):
        with patch.object(watch, "host_headroom", return_value=True), \
             patch.object(watch.time, "monotonic_ns", side_effect=[0, 100_000_000, 350_000_000]), \
             patch.object(watch.time, "clock_gettime_ns", side_effect=[0, 100_000_000, 350_000_000]), \
             patch.object(watch, "state", return_value=(False, 0)), \
             patch.object(watch, "stop_owned", return_value=0):
            self.assertEqual({"status": "timeout", "exit_code": 0}, watch.watch(self.container, self.nonce, .3))

    def test_clock_disagreement_after_inspection_is_rejected(self):
        with patch.object(watch, "host_headroom", return_value=True), \
             patch.object(watch.time, "monotonic_ns", side_effect=[0, 100_000_000, 200_000_000]), \
             patch.object(watch.time, "clock_gettime_ns", side_effect=[0, 100_000_000, 800_000_000]), \
             patch.object(watch, "state", return_value=(False, 0)), \
             patch.object(watch, "stop_owned", return_value=0):
            self.assertEqual({"status": "invalid-clock", "exit_code": 0}, watch.watch(self.container, self.nonce, 2))

    def test_unobserved_exit_cannot_claim_observed_execution(self):
        with patch.object(watch, "host_headroom", return_value=True), \
             patch.object(watch.time, "monotonic_ns", side_effect=[0, 100_000_000, 150_000_000]), \
             patch.object(watch.time, "clock_gettime_ns", side_effect=[0, 100_000_000, 150_000_000]), \
             patch.object(watch, "state", return_value=(False, 0)):
            self.assertEqual({"status": "unobserved-exit", "exit_code": 0}, watch.watch(self.container, self.nonce, 1))

    def test_observed_nonzero_exit_is_failure(self):
        with patch.object(watch, "host_headroom", return_value=True), \
             patch.object(watch.time, "monotonic_ns", side_effect=[0, 100_000_000, 150_000_000, 200_000_000, 250_000_000]), \
             patch.object(watch.time, "clock_gettime_ns", side_effect=[0, 100_000_000, 150_000_000, 200_000_000, 250_000_000]), \
             patch.object(watch.time, "sleep"), patch.object(watch, "state", side_effect=[(True, 0), (False, 7)]):
            self.assertEqual({"status": "failed", "exit_code": 7}, watch.watch(self.container, self.nonce, 1))

    def test_lost_host_reserve_stops_owned_container(self):
        with patch.object(watch, "host_headroom", return_value=False), \
             patch.object(watch, "stop_owned", return_value=137) as stop:
            self.assertEqual({"status": "resource-stop", "exit_code": 137}, watch.watch(self.container, self.nonce, 2))
            stop.assert_called_once_with(self.container, self.nonce)

    def test_unavailable_headroom_cannot_pass(self):
        with patch.object(watch, "host_headroom", side_effect=ValueError("unknown")), \
             patch.object(watch, "stop_owned", return_value=137):
            self.assertEqual("watch-error", watch.watch(self.container, self.nonce, 2)["status"])

    def test_unverifiable_ownership_fails_closed(self):
        with patch.object(watch, "host_headroom", return_value=True), \
             patch.object(watch, "state", side_effect=ValueError("unknown")), \
             patch.object(watch, "docker") as docker:
            result = watch.watch(self.container, self.nonce, 1)
            self.assertEqual("watch-error", result["status"])
            docker.assert_not_called()


if __name__ == "__main__":
    unittest.main()
