"""Guard regression: changed or duplicate translator audit sources receive stale census references."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("shared_translator_audits", ROOT / "scripts/h55/module-times/shared_translator_audits.py")
controls = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controls)

class SharedTranslatorAudits(unittest.TestCase):
    def test_source_binding_and_duplicate_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = "tests/directruntime-20261104/shared-translator/ApiSignatures.lean"
            source = root / path
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            doc = root / controls.ROLES[path][1]
            doc.parent.mkdir(parents=True)
            doc.write_text("static note\n")
            item = {"candidate": {"path": path, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}, "status": "no-supplied-current-reference"}
            self.assertEqual([path], [r["candidate"]["path"] for r in controls.classify(root, {"rows": [item]})])
            with self.assertRaisesRegex(ValueError, "duplicate"):
                controls.classify(root, {"rows": [item, item]})
            source.write_text("changed\n")
            with self.assertRaisesRegex(ValueError, "differs"):
                controls.classify(root, {"rows": [item]})

if __name__ == "__main__":
    unittest.main()
