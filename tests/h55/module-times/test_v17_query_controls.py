"""Guard regression: stale or duplicate query templates gain current census references."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("v17_query_controls", ROOT / "scripts/h55/module-times/v17_query_controls.py")
controls = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controls)

class V17Queries(unittest.TestCase):
    def test_source_and_driver_hashes_and_duplicate_refusal(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = controls.PREFIX + "roadmap-v17-creation-try-query.lean"
            source = root / path
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            driver = root / controls.PREFIX / "roadmap-v17-creation-try.py"
            driver.write_text("# fixture\n")
            item = {"candidate": {"path": path, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}, "status": "no-supplied-current-reference"}
            row = controls.classify(root, {"rows": [item]})[0]
            self.assertEqual(hashlib.sha256(driver.read_bytes()).hexdigest(), row["driver_sha256"][controls.PREFIX + "roadmap-v17-creation-try.py"])
            with self.assertRaisesRegex(ValueError, "duplicate"):
                controls.classify(root, {"rows": [item, item]})
            source.write_text("changed")
            with self.assertRaisesRegex(ValueError, "differs"):
                controls.classify(root, {"rows": [item]})

if __name__ == "__main__":
    unittest.main()
