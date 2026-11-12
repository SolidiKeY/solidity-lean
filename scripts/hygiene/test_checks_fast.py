#!/usr/bin/env python3
"""Storage tests for scripts/ci/checks-fast.sh: where logs and status records go, and that
storage failures fail closed. Each case runs a copy of checks-fast.sh in a throwaway Git
repository whose check scripts are stubs, so no real check runs.

Usage: python3 -B scripts/hygiene/test_checks_fast.py [-v]
"""
import os, shutil, subprocess, sys, tempfile, unittest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SCRIPT = os.path.join(ROOT, "scripts/ci/checks-fast.sh")
OK = "exit 0\n"
# Deletes the directory holding its own log, so checks-fast cannot write its status record.
LOSE_STATUS = 'rm -rf "$(dirname "$(readlink /proc/$$/fd/1)")"\n'


class ChecksFastStorage(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="checks-fast-test.")
        self.repo = os.path.join(self.tmp, "repo")
        os.makedirs(os.path.join(self.repo, "scripts/ci"))
        shutil.copy(SCRIPT, os.path.join(self.repo, "scripts/ci/checks-fast.sh"))
        self.stub("scripts/check-evidence-files.sh", OK)    # check `evidence-files`
        self.stub("scripts/check-private-paths.sh", OK)     # check `private-paths`
        for args in (["init", "-q"], ["add", "-A"],
                     ["-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "stubs"]):
            subprocess.run(["git", *args], cwd=self.repo, check=True, capture_output=True)

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def stub(self, rel, body):
        with open(os.path.join(self.repo, rel), "w") as f:
            f.write("#!/usr/bin/env bash\n" + body)

    def run_checks(self, *names, tmpdir=None, keep=False):
        env = {k: v for k, v in os.environ.items() if k not in ("TMPDIR", "CHECKS_FAST_KEEP_LOGS")}
        if tmpdir is not None: env["TMPDIR"] = tmpdir
        if keep: env["CHECKS_FAST_KEEP_LOGS"] = "1"
        return subprocess.run(["bash", "scripts/ci/checks-fast.sh", *names], cwd=self.repo,
                              env=env, capture_output=True, text=True, timeout=120)

    def spools(self, where):
        return [d for d in os.listdir(where) if d.startswith("checks-fast.")]

    def test_default_uses_git_directory_not_tmp(self):
        r = self.run_checks("evidence-files", keep=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("PASS evidence-files", r.stdout)
        logs = r.stdout.split("checks-fast: logs in ")[1].strip()
        self.assertEqual(os.path.dirname(logs), os.path.realpath(os.path.join(self.repo, ".git")))

    def test_default_cleans_up(self):
        r = self.run_checks("evidence-files")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(self.spools(os.path.join(self.repo, ".git")), [])

    def test_explicit_tmpdir_is_honoured(self):
        spool = os.path.join(self.tmp, "spool"); os.mkdir(spool)
        r = self.run_checks("evidence-files", tmpdir=spool, keep=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(len(self.spools(spool)), 1)
        self.assertEqual(self.spools(os.path.join(self.repo, ".git")), [])

    def test_missing_storage_refuses_before_checks(self):
        marker = os.path.join(self.tmp, "ran")
        self.stub("scripts/check-evidence-files.sh", f'touch "{marker}"\n')
        r = self.run_checks("evidence-files", tmpdir=os.path.join(self.tmp, "absent"))
        self.assertEqual(r.returncode, 2, r.stdout + r.stderr)
        self.assertIn("storage error: cannot create a log directory", r.stderr)
        self.assertNotIn("PASS", r.stdout)
        self.assertFalse(os.path.exists(marker), "a check ran without storage")

    def test_storage_that_is_a_file_refuses(self):
        blocker = os.path.join(self.tmp, "file"); open(blocker, "w").close()
        r = self.run_checks("evidence-files", tmpdir=blocker)
        self.assertEqual(r.returncode, 2, r.stdout + r.stderr)
        self.assertIn("storage error", r.stderr)

    def test_lost_status_record_fails_closed(self):
        self.stub("scripts/check-evidence-files.sh", LOSE_STATUS)
        r = self.run_checks("evidence-files", "private-paths", "--serial")
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("FAIL evidence-files (storage error: status record missing", r.stdout)
        self.assertNotIn("PASS evidence-files", r.stdout)
        self.assertIn("(no log output: storage error or a silent failure)", r.stdout)

    def test_status_path_blocked_fails_closed(self):
        # A status path that cannot be written as a file is a missing record.
        self.stub("scripts/check-evidence-files.sh",
                  'd="$(dirname "$(readlink /proc/$$/fd/1)")"; mkdir "$d/evidence-files.status"\n')
        r = self.run_checks("evidence-files")
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("FAIL evidence-files (storage error: status record missing", r.stdout)

    def test_failing_check_still_reports_exit_and_tail(self):
        self.stub("scripts/check-evidence-files.sh", "echo broken-evidence; exit 3\n")
        r = self.run_checks("evidence-files")
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("(exit 3)", r.stdout)
        self.assertIn("broken-evidence", r.stdout)


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], *sys.argv[1:]])
