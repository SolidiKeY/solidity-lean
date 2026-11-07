"""Guard regression: stale or duplicate audit helpers gain current census references."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("evm_audit_helpers", ROOT / "scripts/h55/module-times/evm_audit_helpers.py")
controls = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controls)

class AuditHelpers(unittest.TestCase):
    def test_source_and_driver_hashes_and_duplicate_refusal(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = controls.PREFIX + "Closed.lean"
            source = root / path
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            driver = root / controls.PREFIX / "closed_census.py"
            driver.write_text("# fixture\n")
            item = {"candidate": {"path": path, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}, "status": "no-supplied-current-reference"}
            row = controls.classify(root, {"rows": [item]})[0]
            self.assertEqual(hashlib.sha256(driver.read_bytes()).hexdigest(), row["driver_sha256"][controls.PREFIX + "closed_census.py"])
            with self.assertRaisesRegex(ValueError, "duplicate"):
                controls.classify(root, {"rows": [item, item]})
            source.write_text("changed")
            with self.assertRaisesRegex(ValueError, "differs"):
                controls.classify(root, {"rows": [item]})

if __name__ == "__main__":
    unittest.main()
