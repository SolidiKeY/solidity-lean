"""Guard H44 regressions: approved-source JSON disguises and hidden root-history additions.

Controls generate oversized payloads only inside disposable Git repositories.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import shlex
import sys
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

    def check_approved_json_is_data(self, body):
        approval = self.root / "scripts/h55/result-size-cache/approved-source.json"
        approval.parent.mkdir(parents=True)
        approval.write_text(json.dumps({"large.py": hashlib.sha256(body).hexdigest()}))
        self.git("add", "scripts/h55/result-size-cache/approved-source.json")
        self.git("commit", "-qm", "trusted approval fixture")
        self.base = self.git("rev-parse", "HEAD").strip()
        (self.root / "large.py").write_bytes(body)
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("path") == "large.py" and r.get("kind") == "data" and r.get("result") == "fail" for r in rows))

    def test_approved_long_integer_json_does_not_gain_source_limit(self):
        self.check_approved_json_is_data(b"1" * 102401)

    def test_approved_deep_json_does_not_gain_source_limit(self):
        self.check_approved_json_is_data(b"[" * 60000 + b"0" + b"]" * 60000)

    def test_unrelated_root_addition_cannot_hide_behind_later_deletion(self):
        original_branch = self.git("symbolic-ref", "--short", "HEAD").strip()
        self.git("checkout", "--orphan", "historical")
        (self.root / "big.dat").write_bytes(b"x" * 102401)
        self.git("add", ".")
        self.git("commit", "-qm", "root bulk addition")
        root_commit = self.git("rev-parse", "HEAD").strip()
        self.git("rm", "big.dat")
        self.git("commit", "-qm", "delete before merge")
        self.git("checkout", original_branch)
        self.git("merge", "--allow-unrelated-histories", "--no-edit", "historical")
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("scope") == "commit:" + root_commit and r.get("path") == "big.dat" and r.get("result") == "fail" for r in rows))

    def test_replacement_refs_cannot_hide_historical_bulk(self):
        (self.root / "big.dat").write_bytes(b"x" * 102401)
        self.git("add", "big.dat")
        self.git("commit", "-qm", "bulk addition")
        addition = self.git("rev-parse", "HEAD").strip()
        self.git("rm", "big.dat")
        self.git("commit", "-qm", "delete bulk")
        empty = self.git("commit-tree", self.base + "^{tree}", "-p", self.base, "-m", "replacement fixture").strip()
        self.git("replace", addition, empty)
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("path") == "big.dat" and r.get("result") == "fail" for r in rows))

    def test_shallow_and_grafted_histories_refused(self):
        (self.root / "small").write_text("small")
        self.git("add", "small")
        self.git("commit", "-qm", "second")
        tip = self.git("rev-parse", "HEAD").strip()
        shallow = self.root / self.git("rev-parse", "--git-path", "shallow").strip()
        shallow.write_text(tip + "\n")
        result = subprocess.run(["python3", str(SCRIPT), self.base], cwd=self.root, capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("shallow history", result.stderr)
        shallow.unlink()
        grafts = self.root / self.git("rev-parse", "--git-path", "info/grafts").strip()
        grafts.parent.mkdir(exist_ok=True)
        grafts.write_text(tip + " " + self.base + "\n")
        result = subprocess.run(["python3", str(SCRIPT), self.base], cwd=self.root, capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("grafted history", result.stderr)

    def test_clean_filter_cannot_hide_oversized_raw_worktree_bytes(self):
        transform = self.root / ".git/clean-fixture.py"
        transform.write_text("import sys; sys.stdin.buffer.read(); sys.stdout.write('{}')\n")
        self.git("config", "filter.fixture.clean", shlex.join([sys.executable, str(transform)]))
        (self.root / ".gitattributes").write_text("old.json filter=fixture\n")
        self.git("add", ".gitattributes")
        self.git("commit", "-qm", "filter fixture")
        self.base = self.git("rev-parse", "HEAD").strip()
        (self.root / "old.json").write_bytes(b"x" * 102401)
        self.assertEqual(self.git("diff", "--name-only"), "")
        result = subprocess.run(["python3", str(SCRIPT), self.base], cwd=self.root, capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("transforming Git attributes", result.stderr)

    def test_staging_after_captured_inventory_cannot_yield_pass(self):
        (self.root / "seed.dat").write_text("small")
        driver = self.root / ".git/census-race.py"
        driver.write_text("import builtins,importlib.util,pathlib,subprocess,sys\n"
            + "spec=importlib.util.spec_from_file_location('gate'," + repr(str(SCRIPT)) + ")\n"
            + "gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)\n"
            + "original=builtins.print;changed=False\n"
            + "def intercept(*a,**kw):\n global changed\n original(*a,**kw)\n if not changed:\n  changed=True\n  pathlib.Path('late.dat').write_bytes(b'x'*102401)\n  subprocess.run(['git','add','late.dat'],check=True)\n"
            + "builtins.print=intercept\n"
            + "try: sys.exit(gate.main())\n"
            + "except RuntimeError as e: sys.stderr.write(str(e));sys.exit(2)\n")
        result = subprocess.run([sys.executable, str(driver), self.base], cwd=self.root, capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("repository inputs changed", result.stderr)
        self.assertFalse(any(row.get("summary") == "pass" for row in map(json.loads, result.stdout.splitlines())))

    def test_index_flags_and_fifo_fail_closed(self):
        self.git("update-index", "--assume-unchanged", "old.json")
        p = subprocess.run(["python3", str(SCRIPT), self.base], cwd=self.root, capture_output=True)
        self.assertEqual(p.returncode, 2)
        self.git("update-index", "--no-assume-unchanged", "old.json")
        (self.root / "old.json").unlink()
        os.mkfifo(self.root / "old.json")
        p = subprocess.run(["python3", str(SCRIPT), self.base], cwd=self.root, capture_output=True, timeout=3)
        self.assertEqual(p.returncode, 2)

    def test_staged_unusual_path_and_binary_cannot_bypass(self):
        name = "nested\nline\tdata.py"
        (self.root / name).write_bytes(b"\0" * 102401)
        self.git("add", name)
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("scope") == "staged" and r.get("path") == name and
                            r.get("kind") == "data" and r.get("result") == "fail" for r in rows))

    def test_forced_ignored_file_is_checked_when_staged(self):
        (self.root / ".gitignore").write_text("ignored.bin\n")
        (self.root / "ignored.bin").write_bytes(b"x" * 102401)
        self.git("add", "-f", "ignored.bin")
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("scope") == "staged" and r.get("path") == "ignored.bin" and
                            r.get("result") == "fail" for r in rows))

    def test_skip_worktree_is_rejected(self):
        self.git("update-index", "--skip-worktree", "old.json")
        p = subprocess.run(["python3", str(SCRIPT), self.base], cwd=self.root, capture_output=True, text=True)
        self.assertEqual(p.returncode, 2)
        self.assertIn("skip-worktree or assume-unchanged", p.stderr)

    def test_non_utf8_leading_dash_path_is_censused(self):
        name = os.fsdecode(b"-raw-\xff.bin")
        (self.root / name).write_bytes(b"x" * 102401)
        self.git("add", "--", name)
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("scope") == "staged" and r.get("path") == name and
                            r.get("result") == "fail" for r in rows))

    def test_oversized_renamed_content_is_checked(self):
        (self.root / "old.json").write_bytes(b"x" * 102401)
        self.git("add", "old.json")
        self.git("commit", "-qm", "oversized baseline")
        self.base = self.git("rev-parse", "HEAD").strip()
        self.git("mv", "old.json", "renamed.json")
        self.assertIn("R100", self.git("diff", "--cached", "--name-status", "-M"))
        status, rows = self.run_gate()
        self.assertEqual(status, 1)
        self.assertTrue(any(r.get("scope") == "staged" and r.get("path") == "renamed.json" and
                            r.get("result") == "fail" for r in rows))
        self.assertTrue(any(r.get("scope") == "staged" and r.get("path") == "old.json" and
                            r.get("status") == "D" and r.get("prior_bytes") == 102401 for r in rows))


if __name__ == "__main__":
    unittest.main()
