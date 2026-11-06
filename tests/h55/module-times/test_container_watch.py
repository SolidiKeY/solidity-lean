import importlib.util
import pathlib
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
        with patch.object(watch, "docker", return_value="other|true|0|67108864|67108864|none|16") as docker:
            with self.assertRaises(ValueError):
                watch.stop_owned(self.container, self.nonce)
            self.assertEqual(1, docker.call_count)
            self.assertEqual("inspect", docker.call_args.args[0])

    def test_resource_policy_mismatch_rejected(self):
        for payload in ["b" * 32 + "|true|0|0|0|none|16",
                        "b" * 32 + "|true|0|67108864|134217728|none|16",
                        "b" * 32 + "|true|0|67108864|67108864|bridge|16",
                        "b" * 32 + "|true|0|67108864|67108864|none|0"]:
            with self.subTest(payload=payload), patch.object(watch, "docker", return_value=payload):
                with self.assertRaises(ValueError):
                    watch.state(self.container, self.nonce)
                self.assertEqual((True, 0), watch.state(self.container, self.nonce, check_limits=False))

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
