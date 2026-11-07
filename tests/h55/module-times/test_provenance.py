import importlib.util
import pathlib
import subprocess
import tempfile
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/provenance.py"
spec = importlib.util.spec_from_file_location("provenance", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class Provenance(unittest.TestCase):
    def test_clean_head_changes_and_dirty_tree(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp) / "repo"
            root.mkdir()
            tool = pathlib.Path(tmp) / "tool"
            tool.write_bytes(b"original tool")
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            source = root / "A.lean"
            source.write_text("-- fixture\n")
            subprocess.run(["git", "-C", str(root), "add", "A.lean"], check=True)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture"], check=True)
            head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
            before = module.snapshot(root, head, tool, "A.lean")
            self.assertTrue(module.unchanged(before, module.snapshot(root, head, tool, "A.lean")))
            self.assertFalse(module.unchanged(before, {}))
            self.assertFalse(module.unchanged({"unrelated": 1}, {"unrelated": 1}))
            malformed = {**before, "source_sha256": "not-a-hash"}
            self.assertFalse(module.unchanged(malformed, malformed))
            tool.write_bytes(b"changed tool")
            self.assertFalse(module.unchanged(before, module.snapshot(root, head, tool, "A.lean")))
            with self.assertRaises(ValueError):
                module.snapshot(root, "0" * 40, tool, "A.lean")
            with self.assertRaises(ValueError):
                module.snapshot(root, head, tool, "../A.lean")
            source.write_text("-- changed\n")
            with self.assertRaises(ValueError):
                module.snapshot(root, head, tool, "A.lean")


if __name__ == "__main__":
    unittest.main()
