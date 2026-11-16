"""Private historical request controls; no historical export/proof acceptance."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location("private_language_export", Path(__file__).with_name("export-v2.py"))
v2 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(v2)
BASE = "c7f33cfc9e1b3c8d0e634f0b267971aa2671688d"


class PrivateExportTests(unittest.TestCase):
    def setUp(self):
        directory = Path(tempfile.gettempdir()).resolve()
        if directory.is_relative_to(ROOT):
            directory = ROOT.parent
        self.temp = tempfile.TemporaryDirectory(dir=directory)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.raw = subprocess.check_output(["git", "--no-replace-objects", "show", BASE + ":" + v2.REQUEST], cwd=ROOT)
        self.input = self.root / v2.REQUEST
        self.input.parent.mkdir(parents=True)
        self.input.write_bytes(self.raw)

    def test_exact_historical_json(self):
        self.assertEqual(v2.load_historical_request(self.root), json.loads(self.raw))

    def test_same_size_corruption_refused(self):
        self.input.write_bytes(bytes([self.raw[0] ^ 1]) + self.raw[1:])
        with self.assertRaisesRegex(ValueError, "checksum mismatch"):
            v2.load_historical_request(self.root)

    def test_missing_private_input_has_no_repository_fallback(self):
        self.input.unlink()
        old_open = Path.open
        def guarded_open(path, *args, **kwargs):
            if path.resolve() == ROOT / v2.REQUEST:
                raise AssertionError("repository fallback forbidden")
            return old_open(path, *args, **kwargs)
        with patch.object(Path, "open", guarded_open), self.assertRaises(FileNotFoundError):
            v2.load_historical_request(self.root)

    def test_repository_input_root_refused(self):
        with self.assertRaisesRegex(ValueError, "outside the repository"):
            v2.load_historical_request(ROOT)

    def test_symlink_escape_refused(self):
        outside = self.root / "outside.json"
        outside.write_bytes(self.raw)
        # The declared root is a separate directory; a sibling target escapes it.
        nested = self.root / "nested"
        candidate = nested / v2.REQUEST
        candidate.parent.mkdir(parents=True)
        candidate.symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "escapes"):
            v2.load_historical_request(nested)

    def test_cli_delegates_only_authenticated_value(self):
        output = self.root / "output"
        argv = ["export-v2.py", "--output", str(output), "--historical-input-root", str(self.root)]
        with patch.object(sys, "argv", argv), patch.object(v2.legacy, "export") as exporter:
            v2.main()
        exporter.assert_called_once_with(output, owner_request=json.loads(self.raw))
        self.input.write_bytes(self.raw + b" ")
        with patch.object(sys, "argv", argv), patch.object(v2.legacy, "export") as exporter:
            with self.assertRaisesRegex(ValueError, "checksum mismatch"):
                v2.main()
            exporter.assert_not_called()

    def test_original_branch_guard_precedes_output(self):
        output = self.root / "output"
        with patch.object(v2.legacy, "git", return_value=b"another-branch\n"):
            with self.assertRaises(AssertionError):
                v2.legacy.export(output, owner_request=json.loads(self.raw))
        self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
