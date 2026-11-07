"""Regression: external frozen fixtures must fail closed on tampering or absence."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[4] / "scripts/h62/item2/audit-calculus"))
from bulk_inputs import bulk_bytes


class BulkInputControls(unittest.TestCase):
    def test_unchanged_input_preserves_exact_bytes(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            data = b"reviewed frozen bytes\n"
            source = root / "data.json"
            source.write_bytes(data)
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"fixture": {"path": str(source), "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}}))
            self.assertEqual(bulk_bytes("fixture", manifest), data)
            source.write_bytes(b"tampered frozen bytes\n")
            with self.assertRaisesRegex(ValueError, "checksum"):
                bulk_bytes("fixture", manifest)

    def test_absent_input_has_no_fallback(self):
        with tempfile.TemporaryDirectory() as name:
            manifest = Path(name) / "manifest.json"
            manifest.write_text(json.dumps({"fixture": {"path": str(Path(name) / "missing"), "bytes": 0, "sha256": hashlib.sha256(b"").hexdigest()}}))
            with self.assertRaises(FileNotFoundError):
                bulk_bytes("fixture", manifest)

    def test_relative_input_path_refused(self):
        with tempfile.TemporaryDirectory() as name:
            manifest = Path(name) / "manifest.json"
            manifest.write_text(json.dumps({"fixture": {"path": "relative.json", "bytes": 0, "sha256": "unused"}}))
            with self.assertRaisesRegex(ValueError, "absolute external"):
                bulk_bytes("fixture", manifest)


if __name__ == "__main__":
    unittest.main()
