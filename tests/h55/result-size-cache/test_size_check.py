import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[3] / "scripts/h55/result-size-cache/size_check.py"


class SizeCheck(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.git("init", "-q")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "user.name", "Test")
        (self.root / "old.json").write_text("{}")
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        self.base = self.git("rev-parse", "HEAD").strip()

    def tearDown(self):
        self.tmp.cleanup()

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True)

    def run_gate(self):
        p = subprocess.run(["python3", str(SCRIPT), self.base], cwd=self.root, text=True, capture_output=True)
        self.assertIn(p.returncode, (0, 1), p.stderr)
        return p.returncode, [json.loads(line) for line in p.stdout.splitlines()]

    def test_staged_violation_survives_worktree_replacement(self):
        path = self.root / "data.json"
        path.write_text("x" * 102401)
        self.git("add", "data.json")
        path.write_text("small")
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("scope") == "staged" and r.get("result") == "fail" for r in rows))

    def test_rename_deletion_and_untracked(self):
        self.git("mv", "old.json", "renamed.json")
        (self.root / "new.dat").write_bytes(b"x" * 102401)
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("status") == "D" and r.get("path") == "old.json" and r.get("prior_type") == "blob" and r.get("prior_bytes") == 2 for r in rows))
        self.assertTrue(any(r.get("path") == "renamed.json" for r in rows))
        self.assertTrue(any(r.get("scope") == "untracked" and r.get("result") == "fail" for r in rows))

    def test_code_limit_binary_and_disguised_json(self):
        code = self.root / "code.py"
        code.write_text("# reviewable source\n" * 7000)
        self.assertEqual(self.run_gate()[0], 1)  # source candidates need a trusted exception mechanism
        code.write_bytes(b"\0" * 102401)
        self.assertEqual(self.run_gate()[0], 1)
        code.write_text(json.dumps(["x" * 102401]))
        self.assertEqual(self.run_gate()[0], 1)
        code.write_text("#" * 1048577)
        self.assertEqual(self.run_gate()[0], 1)

    def test_committed_content_and_threshold(self):
        (self.root / "data").write_bytes(b"x" * 102400)
        self.git("add", "data")
        self.git("commit", "-qm", "within limit")
        self.assertEqual(self.run_gate()[0], 0)
        (self.root / "data").write_bytes(b"x" * 102401)
        self.git("add", "data")
        self.git("commit", "-qm", "over limit")
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("scope") == "committed" and r.get("result") == "fail" for r in rows))

    def test_committed_then_deleted_still_fails(self):
        path = self.root / "hidden.dat"
        path.write_bytes(b"x" * 102401)
        self.git("add", "hidden.dat")
        self.git("commit", "-qm", "add")
        self.git("rm", "hidden.dat")
        self.git("commit", "-qm", "delete")
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("scope", "").startswith("commit:") and r.get("result") == "fail" for r in rows))

    def test_only_base_approved_exact_source_is_allowed(self):
        body = ("# source line\n" * 8000).encode()
        approval = self.root / "scripts/h55/result-size-cache/approved-source.json"
        approval.parent.mkdir(parents=True)
        approval.write_text(json.dumps({"large.py": hashlib.sha256(body).hexdigest()}))
        self.git("add", ".")
        self.git("commit", "-qm", "trusted approval")
        self.base = self.git("rev-parse", "HEAD").strip()
        (self.root / "large.py").write_bytes(body)
        self.assertEqual(self.run_gate()[0], 0)
        (self.root / "large.py").write_bytes(body + b"# changed\n")
        self.assertEqual(self.run_gate()[0], 1)
        approval.write_text(json.dumps({"large.py": hashlib.sha256(body + b"# changed\n").hexdigest()}))
        self.assertEqual(self.run_gate()[0], 1)

    def test_large_worktree_census_reports_actual_size(self):
        (self.root / "huge.dat").write_bytes(b"x" * 2000000)
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("path") == "huge.dat" and r.get("bytes") == 2000000 for r in rows))

    def test_index_flags_and_fifo_fail_closed(self):
        self.git("update-index", "--assume-unchanged", "old.json")
        p = subprocess.run(["python3", str(SCRIPT), self.base], cwd=self.root, capture_output=True)
        self.assertEqual(p.returncode, 2)
        self.git("update-index", "--no-assume-unchanged", "old.json")
        (self.root / "old.json").unlink()
        os.mkfifo(self.root / "old.json")
        p = subprocess.run(["python3", str(SCRIPT), self.base], cwd=self.root, capture_output=True, timeout=3)
        self.assertEqual(p.returncode, 2)


if __name__ == "__main__":
    unittest.main()
