"""Real-Git H44 input-authentication controls; no proof results are mocked."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
import bulk_inputs


class ExternalBulkInputControls(unittest.TestCase):
    def test_authenticated_bulk_and_each_tamper_boundary(self):
        for fault in [None, "manifest", "index", "external", "mirror", "unregistered", "symlink"]:
            with self.subTest(fault=fault), tempfile.TemporaryDirectory() as tmp:
                base = Path(tmp); repo = base / "repo"; repo.mkdir()
                root = base / "bulk"; root.mkdir()
                rel = bulk_inputs.PREFIX / "fixture.json"
                mirror = repo / rel; mirror.parent.mkdir(parents=True); mirror.write_bytes(b"frozen")
                external = root / rel; external.parent.mkdir(parents=True); external.write_bytes(b"frozen")
                index = base / "files.json"
                index.write_text(json.dumps({"files": {str(rel): {"bytes": 6, "sha256": hashlib.sha256(b"frozen").hexdigest()}}}))
                pin = repo / bulk_inputs.PREFIX / "bulk-data.json"
                pin.write_text(json.dumps({"schema": 1, "authorization": "H44", "root": str(root), "index": str(index), "index_sha256": hashlib.sha256(index.read_bytes()).hexdigest(), "file_count": 1}))
                def git(*args):
                    subprocess.run(["git", "-c", "user.name=H28 fixture", "-c", "user.email=h28@example.invalid", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args], cwd=repo, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                git("init", "-q"); git("add", str(pin.relative_to(repo))); git("commit", "-qm", "hash anchor fixture")
                if fault == "manifest": pin.write_text(pin.read_text() + " ")
                if fault == "index": index.write_text(index.read_text() + " ")
                if fault == "external": external.write_bytes(b"forged")
                if fault == "mirror": mirror.write_bytes(b"forged")
                if fault == "unregistered":
                    mirror = mirror.with_name("other.json"); mirror.write_bytes(b"frozen")
                if fault == "symlink":
                    external.unlink(); external.symlink_to(mirror)
                if fault is None:
                    self.assertEqual(bulk_inputs.read(repo, mirror), b"frozen")
                    # Tracking the source restores the stronger direct-HEAD gate.
                    git("add", str(rel)); git("commit", "-qm", "tracked fixture")
                    mirror.write_bytes(b"forged"); external.write_bytes(b"forged")
                    with self.assertRaisesRegex(ValueError, "committed input differs"):
                        bulk_inputs.read(repo, mirror)
                else:
                    with self.assertRaises(ValueError): bulk_inputs.read(repo, mirror)
