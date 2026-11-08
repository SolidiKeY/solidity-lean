"""Guard regression: missing or symlinked staged inputs appear as usable fixtures."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("fresh_shared_request", ROOT / "scripts/h55/module-times/fresh_shared_request.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class FreshSharedRequest(unittest.TestCase):
    def test_absent_present_and_symlink(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.assertEqual("absent", module.regular(root, "fixture.json")["status"])
            (root / "fixture.json").write_text("{}")
            self.assertEqual("present-unverified", module.regular(root, "fixture.json")["status"])
            (root / "alias.json").symlink_to(root / "fixture.json")
            with self.assertRaisesRegex(ValueError, "unsafe"):
                module.regular(root, "alias.json")
            (root / "dangling").symlink_to(root / "missing")
            with self.assertRaisesRegex(ValueError, "unsafe"):
                module.regular(root, "dangling/fixture.json")

    def test_dirty_handoff_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            doc = root / module.DOC
            doc.parent.mkdir(parents=True)
            doc.write_text("changed")
            stage = root / "stage"
            stage.mkdir()
            with mock.patch.object(module.subprocess, "check_output", return_value=b"committed"):
                with self.assertRaisesRegex(ValueError, "handoff differs"):
                    module.observe(root, stage, "0" * 40)

    def test_unavailable_staging_root_is_not_empty_inventory(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(ValueError, "invalid staged root"):
                module.observe(Path(tmp), Path(tmp) / "missing", "0" * 40)

if __name__ == "__main__":
    unittest.main()
