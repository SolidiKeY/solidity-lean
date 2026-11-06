"""Negative controls for delivery receipts; no semantic proof success is mocked."""
from pathlib import Path
import hashlib
import json
import subprocess
import tarfile
import tempfile
import unittest
import verify_bulk
import verify_combined


class DeliveryReceiptControls(unittest.TestCase):
    def test_nested_validation_archive_and_tampering(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "validation.tar.gz"
            data = b"immutable validation bytes"
            path.write_bytes(data)
            pin = {"archive": str(path), "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
            manifest = {"candidate_inventory_audit": {"validation": pin}}
            self.assertEqual(verify_bulk.verify_validation_archives(manifest), ["candidate_inventory_audit.validation"])
            for fault in (b"X" + data[1:], data + b"X"):
                path.write_bytes(fault)
                with self.assertRaisesRegex(ValueError, "identity mismatch"):
                    verify_bulk.verify_validation_archives(manifest)
            path.unlink()
            other = Path(tmp) / "other"; other.write_bytes(data); path.symlink_to(other)
            with self.assertRaisesRegex(ValueError, "invalid validation archive"):
                verify_bulk.verify_validation_archives(manifest)

    def test_combined_wrong_member_count_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); repo = root / "repo"; repo.mkdir()
            archive = root / "proof.tar.gz"
            with tarfile.open(archive, "w:gz"):
                pass
            pin = {"archive": str(archive), "bytes": archive.stat().st_size, "sha256": hashlib.sha256(archive.read_bytes()).hexdigest(), "members": 1}
            manifest = repo / "tests/h28-sol/mutation-testing/bulk-data.json"
            manifest.parent.mkdir(parents=True); manifest.write_text(json.dumps({"combined_proof_pack": pin}))
            def git(*args):
                subprocess.run(["git", "-c", "user.name=H28 control", "-c", "user.email=h28@example.invalid", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args], cwd=repo, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            git("init", "-q"); git("add", "."); git("commit", "-qm", "controlled receipt")
            with self.assertRaisesRegex(ValueError, "archive member count mismatch"):
                verify_combined.verify(repo)
