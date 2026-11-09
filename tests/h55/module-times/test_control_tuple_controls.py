"""Guard regression: stale or duplicate control-tuple fixtures gain census references."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("control_tuple_controls", ROOT / "scripts/h55/module-times/control_tuple_controls.py")
controls = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controls)

class ControlTupleTests(unittest.TestCase):
    def test_fixture_binding_and_changed_source_refusal(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = controls.PREFIX + "ObligationControls.lean"
            source = root / path
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            fixture = root / controls.PREFIX / "Obligations.ast.json"
            fixture.write_text("{}")
            doc = root / controls.DOC
            doc.parent.mkdir(parents=True)
            doc.write_text("handoff")
            item = {"candidate": {"path": path, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}, "status": "no-supplied-current-reference"}
            row = controls.classify(root, {"rows": [item]})[0]
            self.assertEqual(hashlib.sha256(fixture.read_bytes()).hexdigest(), row["fixture_sha256"][controls.PREFIX + "Obligations.ast.json"])
            with self.assertRaisesRegex(ValueError, "duplicate"):
                controls.classify(root, {"rows": [item, item]})
            source.write_text("changed")
            with self.assertRaisesRegex(ValueError, "differs"):
                controls.classify(root, {"rows": [item]})

if __name__ == "__main__":
    unittest.main()
