import copy
import importlib.util
import pathlib
import subprocess
import tempfile
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/bound_snapshot.py"
spec = importlib.util.spec_from_file_location("bound_snapshot", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class BoundSnapshot(unittest.TestCase):
    def test_source_tool_cache_and_corrupt_record(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp).resolve()
            root, cache, tool = base / "repo", base / "cache", base / "tool"
            root.mkdir()
            cache.mkdir()
            tool.write_bytes(b"fixture tool")
            (cache / "A.olean").write_bytes(b"fixture cache")
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "A.lean").write_text("-- fixture\n")
            subprocess.run(["git", "-C", str(root), "add", "A.lean"], check=True)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture"], check=True)
            head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
            before = module.capture(root, head, tool, "A.lean", cache)
            self.assertTrue(module.compare(before, module.capture(root, head, tool, "A.lean", cache)))
            malformed = copy.deepcopy(before)
            malformed["cache"]["manifest_sha256"] = "0" * 64
            self.assertFalse(module.compare(malformed, malformed))
            (cache / "A.olean").write_bytes(b"changed cache")
            self.assertFalse(module.compare(before, module.capture(root, head, tool, "A.lean", cache)))
            tool.write_bytes(b"changed tool")
            self.assertFalse(module.compare(before, module.capture(root, head, tool, "A.lean", cache)))
            (root / "A.lean").write_text("-- changed\n")
            with self.assertRaises(ValueError):
                module.capture(root, head, tool, "A.lean", cache)


if __name__ == "__main__":
    unittest.main()
