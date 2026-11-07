"""Controls for `verify_bulk.verify_local`: off the Codex VM it checks the
committed side only, reports `local-only` (never `pass`), and refuses a
changed input or an uncommitted manifest."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import verify_bulk
from archive_io import require  # noqa: F401  (same failure type as the tool)

P = "tests/h28-sol/mutation-testing"


def git(repo, *a):
    subprocess.run(["git", *a], cwd=repo, check=True, capture_output=True)


class LocalControls(unittest.TestCase):
    def make(self, d):
        repo = Path(d)
        git(repo, "init", "-q")
        git(repo, "config", "user.email", "t@t")
        git(repo, "config", "user.name", "t")
        (repo / P / "manifests").mkdir(parents=True)
        data = b'{"x": 1}\n'
        (repo / P / "inv.json").write_bytes(data)
        pin = {"role": "inventory", "path": P + "/inv.json",
               "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
        cache = {"role": "cache_manifest", "path": P + "/evidence/absent.json", "sha256": "0" * 64, "bytes": 1}
        (repo / P / "manifests/m.json").write_text(json.dumps({
            "inventory": pin["path"], "inventory_sha256": pin["sha256"],
            "cache_manifest": cache["path"], "cache_manifest_sha256": cache["sha256"]}))
        (repo / P / "bulk-data.json").write_text(json.dumps({
            "index": "/nonexistent/files.json", "archive": "/nonexistent/a.tgz",
            "backup_bundle": "/nonexistent/b.bundle",
            "frozen_manifest_inputs": {P + "/manifests/m.json": [pin, cache]},
            "retained_reviewable_support_files": [P + "/manifests/m.json"]}))
        git(repo, "add", ".")
        git(repo, "commit", "-qm", "x")
        return repo

    def test_local_only_never_pass(self):
        with tempfile.TemporaryDirectory() as d:
            r = verify_bulk.verify_local(self.make(d))
            self.assertEqual(r["status"], "local-only")
            self.assertEqual(r["absent_codex_vm_only"], [P + "/evidence/absent.json"])
            self.assertEqual(len(r["unverifiable_here"]), 3)

    def test_changed_input_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            repo = self.make(d)
            (repo / P / "inv.json").write_bytes(b'{"x": 2}\n')
            with self.assertRaises(Exception):
                verify_bulk.verify_local(repo)

    def test_uncommitted_manifest_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            repo = self.make(d)
            p = repo / P / "bulk-data.json"
            p.write_text(p.read_text() + " ")
            with self.assertRaises(Exception):
                verify_bulk.verify_local(repo)


if __name__ == "__main__":
    unittest.main()
