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


class PrivateArchiveControls(unittest.TestCase):
    """Guard H145 reads against mutable mirrors, bad pins and altered payloads."""
    def packet(self, root, payload=b"frozen archived bytes", *, digest=None, member="data.json"):
        import subprocess
        data = root / "packet"
        data.mkdir()
        (data / "data.json").write_bytes(payload)
        (data / "bulk-inputs-manifest.json").write_text(json.dumps({"fixture": {
            "path": member, "bytes": len(payload),
            "sha256": digest or hashlib.sha256(payload).hexdigest()}}))
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        subprocess.run(["git", "-C", str(root), "add", "."], check=True)
        subprocess.run(["git", "-C", str(root), "-c", "user.name=control", "-c", "user.email=control@example.invalid", "commit", "-qm", "fixture"], check=True)
        return subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()

    def read(self, root, commit):
        from unittest.mock import patch
        import bulk_inputs
        with patch.dict("os.environ", {"SOLIDITY_COORD_EVIDENCE_REPO": str(root)}), patch.object(bulk_inputs, "ARCHIVE_COMMIT", commit), patch.object(bulk_inputs, "ARCHIVE_DIR", "packet"):
            return bulk_bytes("fixture")

    def test_immutable_commit_ignores_working_mirror(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            commit = self.packet(root)
            (root / "packet/data.json").write_bytes(b"modified working mirror")
            self.assertEqual(self.read(root, commit), b"frozen archived bytes")

    def test_git_replacements_cannot_override_pin(self):
        import subprocess
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            original = self.packet(root)
            changed = b"replacement commit bytes"
            (root / "packet/data.json").write_bytes(changed)
            (root / "packet/bulk-inputs-manifest.json").write_text(json.dumps({"fixture": {
                "path": "data.json", "bytes": len(changed),
                "sha256": hashlib.sha256(changed).hexdigest()}}))
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=control", "-c", "user.email=control@example.invalid", "commit", "-qm", "replacement"], check=True)
            replacement = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
            subprocess.run(["git", "-C", str(root), "replace", original, replacement], check=True)
            self.assertEqual(self.read(root, original), b"frozen archived bytes")

    def test_inherited_git_directory_cannot_redirect_reader(self):
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            commit = self.packet(root)
            with patch.dict("os.environ", {"GIT_DIR": str(root / "missing"), "GIT_OBJECT_DIRECTORY": str(root / "missing")}):
                self.assertEqual(self.read(root, commit), b"frozen archived bytes")

    def test_bad_digest_refused(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            commit = self.packet(root, digest="0" * 64)
            with self.assertRaisesRegex(ValueError, "checksum"):
                self.read(root, commit)

    def test_traversal_refused(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            commit = self.packet(root, member="../data.json")
            with self.assertRaisesRegex(ValueError, "unsafe archive"):
                self.read(root, commit)

    def test_mutable_revision_refused(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            self.packet(root)
            with self.assertRaisesRegex(ValueError, "immutable commit"):
                self.read(root, "HEAD")

    def test_missing_archive_has_no_vm_fallback(self):
        from unittest.mock import patch
        with patch.dict("os.environ", {}, clear=True):
            with self.assertRaisesRegex(FileNotFoundError, "private archive"):
                bulk_bytes("lifetime_roles")


if __name__ == "__main__":
    unittest.main()
