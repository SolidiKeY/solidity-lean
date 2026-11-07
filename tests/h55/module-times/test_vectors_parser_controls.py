"""Guard regression: stale or unrelated parser probes receive static census references."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("vectors_parser_controls", ROOT / "scripts/h55/module-times/vectors_parser_controls.py")
controls = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controls)

class ParserControls(unittest.TestCase):
    def test_source_binding_and_preservation_of_unrelated_rows(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = controls.PREFIX + "ParseProbe.lean"
            source = root / path
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            candidate = {"path": path, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            index = {"rows": [{"candidate": candidate, "status": "no-supplied-current-reference"},
                              {"candidate": {"path": controls.PREFIX + "Other.lean"}, "status": "no-supplied-current-reference"}]}
            rows = controls.classify(root, index)
            self.assertEqual([path], [row["candidate"]["path"] for row in rows])
            source.write_text("changed\n")
            with self.assertRaisesRegex(ValueError, "differs"):
                controls.classify(root, index)

    def test_duplicate_candidate_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = controls.PREFIX + "ParseContext.lean"
            source = root / path
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            item = {"candidate": {"path": path, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}, "status": "no-supplied-current-reference"}
            with self.assertRaisesRegex(ValueError, "duplicate"):
                controls.classify(root, {"rows": [item, item]})

if __name__ == "__main__":
    unittest.main()
