import fcntl
import importlib.util
import pathlib
import subprocess
import tempfile
import unittest
from unittest.mock import patch

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/observation_bridge.py"
spec = importlib.util.spec_from_file_location("observation_bridge", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class ObservationBridge(unittest.TestCase):
    def test_untrusted_success_and_cache_drift(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp).resolve()
            root, cache, tool = base / "repo", base / "cache", base / "tool"
            root.mkdir()
            cache.mkdir()
            tool.write_bytes(b"test tool")
            (cache / "object.olean").write_bytes(b"old")
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "A.lean").write_text("-- fixture\n")
            subprocess.run(["git", "-C", str(root), "add", "A.lean"], check=True)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture"], check=True)
            head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
            with patch.object(module, "LOCK", base / "writer.lock"):
                good = module.observe(root, head, tool, "A.lean", cache,
                                      lambda: {"status": "exited", "exit_code": 0})
                self.assertEqual("untrusted-observation", good["status"])
                bad = module.observe(root, head, tool, "A.lean", cache,
                                     lambda: {"status": "exited", "exit_code": 1})
                self.assertEqual("failed-observation", bad["status"])
                failure = module.observe(root, head, tool, "A.lean", cache,
                                         lambda: (_ for _ in ()).throw(RuntimeError("fixture")))
                self.assertEqual("action-error", failure["status"])
                with patch.object(module.time, "monotonic_ns", side_effect=[0, 1]), \
                     patch.object(module.time, "clock_gettime_ns", side_effect=[0, 2_000_000_000]):
                    bad_clock = module.observe(root, head, tool, "A.lean", cache,
                                               lambda: {"status": "exited", "exit_code": 0})
                self.assertEqual("invalid-time", bad_clock["status"])
                with (base / "writer.lock").open("a") as held:
                    fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    not_called = lambda: self.fail("action ran without lock")
                    self.assertEqual("snapshot-or-lock-error", module.observe(root, head, tool, "A.lean", cache, not_called)["status"])
                def mutate():
                    (cache / "object.olean").write_bytes(b"new")
                    return {"status": "exited", "exit_code": 0}
                self.assertEqual("input-drift", module.observe(root, head, tool, "A.lean", cache, mutate)["status"])


if __name__ == "__main__":
    unittest.main()
