#!/usr/bin/env python3
"""Unit tests for run_changed.py (stdlib only; builds throwaway git repositories)."""
import contextlib, io, json, os, subprocess, sys, tempfile, unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_changed as rc

WF = """name: demo
on: [push, pull_request]
jobs:
  quick:
    runs-on: ubuntu-latest
    env:
      MODE: strict
    steps:
      - uses: actions/checkout@v4
      - name: Self-test
        run: python3 -B scripts/tool.py
      - run: |
          test "$MODE" = strict
          echo ok
  heavy:
    runs-on: ubuntu-latest
    steps:
      - uses: leanprover/lean-action@v1
      - run: lake build Foo
      - name: After build
        run: node scripts/reads-build.mjs
      - name: Download
        run: curl -O https://example.invalid/x
      - name: Nightly
        if: ${{ github.event_name == 'schedule' }}
        run: echo nightly
"""


def sh(cwd, *args):
    subprocess.run(args, cwd=cwd, check=True, capture_output=True)


class Yaml(unittest.TestCase):
    def test_workflow_shapes(self):
        wf = rc.yaml_load(WF)
        self.assertEqual(wf["on"], ["push", "pull_request"])
        steps = wf["jobs"]["quick"]["steps"]
        self.assertEqual(steps[0], {"uses": "actions/checkout@v4"})
        self.assertEqual(steps[2]["run"], 'test "$MODE" = strict\necho ok\n')
        self.assertEqual(wf["jobs"]["quick"]["env"], {"MODE": "strict"})

    def test_step_classification(self):
        got = {s["name"]: s["skip"] for s in rc.workflow_steps("demo.yml", WF)}
        self.assertIsNone(got["Self-test"])
        self.assertEqual(got["lake build Foo"], "needs Lean")
        self.assertTrue(got["After build"].startswith("after skipped setup step"))
        self.assertEqual(got["Download"], "needs network")
        self.assertEqual(got["Nightly"], "schedule/dispatch-only step")

    def test_dispatch_only_workflow_is_skipped(self):
        steps = list(rc.workflow_steps("d.yml", "on:\n  workflow_dispatch:\njobs:\n  a:\n    steps:\n      - run: echo hi\n"))
        self.assertEqual(steps[0]["skip"], "workflow not run on push/pull_request")

    def test_path_in_run_globs(self):
        self.assertTrue(rc.path_in_run("scripts/trust/trust-x.test.mjs", "node --test scripts/trust/trust-*.test.mjs"))
        self.assertFalse(rc.path_in_run("scripts/other.mjs", "node scripts/tool.mjs"))


class EndToEnd(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.r = self.tmp.name
        sh(self.r, "git", "init", "-q", "-b", "master")
        sh(self.r, "git", "config", "user.email", "t@t")
        sh(self.r, "git", "config", "user.name", "t")
        self.write("scripts/tool.py", "print('ok')\n")
        self.write("scripts/ci/checks-fast.sh", "checks=$(cat <<'EOF'\nfast\tpython3 -B scripts/covered_test.py\nEOF\n)\n")
        self.base = self.commit("base")

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        p = os.path.join(self.r, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w") as f:
            f.write(text)

    def commit(self, msg):
        sh(self.r, "git", "add", "-A")
        sh(self.r, "git", "commit", "-q", "-m", msg)
        return subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.r, capture_output=True, text=True).stdout.strip()

    def run_rc(self, head, *extra):
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
            code = rc.main(["--base", self.base, "--head", head, "--repo", self.r, "--json", "--workdir", self.r + "/..", *extra])
        try:
            return code, json.loads(out.getvalue())
        except ValueError:
            return code, None

    def test_failing_new_test_fails_run(self):
        self.write("scripts/test_new.py", "import sys\nif __name__ == '__main__':\n    sys.exit(3)\n")
        code, res = self.run_rc(self.commit("bad test"))
        self.assertEqual(code, 1)
        [item] = [i for i in res["items"] if i["name"] == "scripts/test_new.py"]
        self.assertEqual((item["status"], item["base"]), ("fail", "absent"))

    def test_unblocked_kind_is_advisory(self):
        self.write("scripts/test_new.py", "import sys\nif __name__ == '__main__':\n    sys.exit(3)\n")
        code, res = self.run_rc(self.commit("bad test"), "--block", "workflow")
        self.assertEqual(code, 0)
        [item] = [i for i in res["items"] if i["name"] == "scripts/test_new.py"]
        self.assertEqual(item["status"], "advisory")

    def test_passing_test_and_workflow(self):
        self.write("scripts/test_new.py", "if __name__ == '__main__':\n    pass\n")
        self.write(".github/workflows/demo.yml", WF)
        code, res = self.run_rc(self.commit("ok"))
        self.assertEqual(code, 0)
        ran = {i["name"]: i["status"] for i in res["items"] if not i["skip"]}
        self.assertEqual(ran["Self-test"], "pass")
        self.assertEqual(ran["scripts/test_new.py"], "pass")

    def test_preexisting_failure_does_not_fail(self):
        self.write("scripts/tool.py", "raise SystemExit(1)\n")
        self.write(".github/workflows/demo.yml", "on: push\njobs:\n  a:\n    steps:\n      - run: python3 -B scripts/tool.py\n")
        self.base = self.commit("broken on base")
        self.write("scripts/tool.py", "raise SystemExit(2)\n")
        code, res = self.run_rc(self.commit("still broken"))
        self.assertEqual(code, 0)
        self.assertEqual(res["items"][0]["status"], "pre-existing")

    def test_lean_is_never_run(self):
        self.write("scripts/test_lean.py", "import subprocess, sys\nif __name__ == '__main__':\n"
                   "    sys.exit(subprocess.run(['la' + 'ke', 'build']).returncode)\n")
        code, res = self.run_rc(self.commit("lean"))
        self.assertEqual(code, 0)
        self.assertEqual(res["items"][0]["status"], "needs-lean")

    def test_covered_by_checks_fast(self):
        self.write("scripts/covered_test.py", "if __name__ == '__main__':\n    raise SystemExit(1)\n")
        code, res = self.run_rc(self.commit("covered"))
        self.assertEqual(code, 0)
        self.assertTrue(res["items"][0]["skip"].startswith("covered"))

    def test_bad_revision_is_usage_error(self):
        code, _ = self.run_rc("no-such-rev")
        self.assertEqual(code, 2)


if __name__ == "__main__":
    unittest.main()
