"""Guard regression: changed or duplicate shared local control sources receive stale census references."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("shared_local_controls", ROOT / "scripts/h55/module-times/shared_local_controls.py")
controls = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controls)

class SharedLocalControls(unittest.TestCase):
    def test_source_binding_and_duplicate_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = "tests/directruntime-20261104/shared-translator/AddressLocalControls.lean"
            source = root / path
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            doc = root / controls.DOC
            doc.parent.mkdir(parents=True)
            doc.write_text("static note\n")
            item = {"candidate": {"path": path, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}, "status": "no-supplied-current-reference"}
            rows = controls.classify(root, {"rows": [item]})
            self.assertEqual([path], [r["candidate"]["path"] for r in rows])
            self.assertFalse(rows[0]["fixture_present"])
            self.assertIsNone(rows[0]["fixture_sha256"])
            with self.assertRaisesRegex(ValueError, "duplicate"):
                controls.classify(root, {"rows": [item, item]})
            source.write_text("changed\n")
            with self.assertRaisesRegex(ValueError, "differs"):
                controls.classify(root, {"rows": [item]})

if __name__ == "__main__":
    unittest.main()
