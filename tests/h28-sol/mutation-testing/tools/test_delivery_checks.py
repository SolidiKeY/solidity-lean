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

    def test_committed_member_manifest_rejects_member_tampering(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); repo = root / "repo"; repo.mkdir()
            payload = root / "data.txt"; payload.write_bytes(b"payload")
            archive = root / "data.tar.gz"
            with tarfile.open(archive, "w:gz") as tar:
                tar.add(payload, arcname="data.txt")
            relative = "tests/h28-sol/mutation-testing/evidence/member-manifest.json"
            target = repo / relative; target.parent.mkdir(parents=True)
            pin = {"archive": str(archive), "bytes": archive.stat().st_size, "sha256": hashlib.sha256(archive.read_bytes()).hexdigest(), "member_manifest": relative}
            def git(*args):
                subprocess.run(["git", "-c", "user.name=H28 control", "-c", "user.email=h28@example.invalid", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args], cwd=repo, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            git("init", "-q")
            with self.assertRaisesRegex(ValueError, "member manifest pin missing archive"):
                verify_bulk.verify_validation_archives({"proof_pack": {"member_manifest": relative}}, repo)
            for fault in (None, "hash", "size", "membership"):
                members = {"data.txt": {"bytes": 7, "sha256": hashlib.sha256(b"payload").hexdigest()}}
                if fault == "hash": members["data.txt"]["sha256"] = "0" * 64
                if fault == "size": members["data.txt"]["bytes"] = 8
                if fault == "membership": members["missing.txt"] = members.pop("data.txt")
                target.write_text(json.dumps({"schema": 1, "authorization": "H44", "archive": pin["archive"], "archive_bytes": pin["bytes"], "archive_sha256": pin["sha256"], "members": members}))
                (repo / "tests/h28-sol/mutation-testing/bulk-data.json").write_text(json.dumps({"combined_proof_pack": pin}))
                git("add", "."); git("commit", "-qm", "controlled member receipt")
                if fault is None:
                    self.assertEqual(verify_bulk.verify_h44_member_manifest(repo, pin), 1)
                    self.assertEqual(verify_bulk.verify_validation_archives({"rollback_proof_pack": pin}, repo), ["rollback_proof_pack"])
                    with self.assertRaisesRegex(ValueError, "archive member count mismatch"):
                        verify_bulk.verify_h44_member_manifest(repo, {**pin, "members": 2})
                else:
                    with self.assertRaisesRegex(ValueError, "archive member.*mismatch"):
                        verify_bulk.verify_h44_member_manifest(repo, pin)
                    with self.assertRaisesRegex(ValueError, "archive member.*mismatch"):
                        verify_combined.verify(repo)
                    with self.assertRaisesRegex(ValueError, "archive member.*mismatch"):
                        verify_bulk.verify_validation_archives({"rollback_proof_pack": pin}, repo)

    def test_archive_authentication_precedes_member_parsing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); repo = root / "repo"; repo.mkdir()
            archive = root / "untrusted.tar.gz"; archive.write_bytes(b"not a tar stream")
            pin = {"archive": str(archive), "bytes": archive.stat().st_size, "sha256": "0" * 64,
                   "member_manifest": "tests/h28-sol/mutation-testing/evidence/missing.json"}
            target = repo / "tests/h28-sol/mutation-testing/bulk-data.json"
            target.parent.mkdir(parents=True); target.write_text(json.dumps({"combined_proof_pack": pin}))
            def git(*args):
                subprocess.run(["git", "-c", "user.name=H28 control", "-c", "user.email=h28@example.invalid", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args], cwd=repo, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            git("init", "-q"); git("add", "."); git("commit", "-qm", "untrusted archive control")
            with self.assertRaisesRegex(ValueError, "archive hash mismatch"):
                verify_combined.verify(repo)
