"""Archive controls; these are not semantic proof witnesses."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import archive_io
import bulk_inputs
import verify_bulk


def git(repo, *args):
    subprocess.run(["git", "-c", "user.name=H28 fixture", "-c", "user.email=h28@example.invalid", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args], cwd=repo, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


class ArchiveInputControls(unittest.TestCase):
    def test_failure_check_remains_active_with_optimization(self):
        program = "import archive_io; archive_io.require(False, str(12345))"
        result = subprocess.run([sys.executable, "-O", "-B", "-c", program], cwd=Path(__file__).resolve().parent, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("ValueError: 12345", result.stderr)

    def test_json_authentication_precedes_parsing_or_use(self):
        for fault in [None, "mirror", "external", "index", "manifest"]:
            with self.subTest(fault=fault), tempfile.TemporaryDirectory() as tmp:
                base = Path(tmp); repo = base / "repo"; repo.mkdir(); root = base / "bulk"
                rel = bulk_inputs.PREFIX / "evidence/fixture/catalog.json"
                mirror = repo / rel; mirror.parent.mkdir(parents=True)
                data = json.dumps({"frozen": True}).encode(); forged = json.dumps({"forged": True}).encode()
                mirror.write_bytes(data)
                external = root / rel; external.parent.mkdir(parents=True); external.write_bytes(data)
                index = base / "files.json"
                index.write_text(json.dumps({"files": {str(rel): {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}}}))
                pin = repo / bulk_inputs.PREFIX / "bulk-data.json"
                pin.write_text(json.dumps({"schema": 1, "authorization": "H44", "root": str(root), "index": str(index), "index_sha256": hashlib.sha256(index.read_bytes()).hexdigest(), "file_count": 1}))
                git(repo, "init", "-q"); git(repo, "add", str(pin.relative_to(repo))); git(repo, "commit", "-qm", "bulk anchor")
                if fault == "mirror": mirror.write_bytes(forged)
                if fault == "external": external.write_bytes(forged)
                if fault == "index": index.write_text(index.read_text() + " ")
                if fault == "manifest": pin.write_text(pin.read_text() + " ")
                if fault is None:
                    self.assertEqual(archive_io.read_json(mirror, repo), {"frozen": True})
                else:
                    with self.assertRaises(ValueError): archive_io.read_json(mirror, repo)

    def test_tracked_mirror_must_match_both_head_and_index(self):
        for fault in ["same-length-committed-change", "different-length-committed-change", "uncommitted-change", "external-change"]:
            with self.subTest(fault=fault), tempfile.TemporaryDirectory() as tmp:
                base = Path(tmp); repo = base / "repo"; repo.mkdir(); root = base / "bulk"
                rel = str(bulk_inputs.PREFIX / "evidence/fixture/verify.py")
                data = b"original indexed source"
                mirror = repo / rel; mirror.parent.mkdir(parents=True); mirror.write_bytes(data)
                external = root / rel; external.parent.mkdir(parents=True); external.write_bytes(data)
                git(repo, "init", "-q"); git(repo, "add", rel); git(repo, "commit", "-qm", "indexed verifier source")
                entries = {rel: {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}}
                manifest = {"root": str(root), "retained_reviewable_support_files": [rel]}
                self.assertEqual(verify_bulk.verify_snapshot_files(repo, manifest, entries), len(data))
                if fault == "external-change":
                    external.write_bytes(b"X" + data[1:])
                else:
                    mirror.write_bytes((b"X" + data[1:]) if fault != "different-length-committed-change" else data + b"changed")
                    if fault != "uncommitted-change":
                        git(repo, "add", rel); git(repo, "commit", "-qm", "HEAD changes without updating sealed index")
                        self.assertEqual(bulk_inputs.read(repo, mirror), mirror.read_bytes())
                with self.assertRaises(ValueError):
                    verify_bulk.verify_snapshot_files(repo, manifest, entries)
