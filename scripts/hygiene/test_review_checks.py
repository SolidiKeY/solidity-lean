#!/usr/bin/env python3
"""Tests for scripts/hygiene/review_checks.py on temporary Git repositories.

Usage: python3 -B scripts/hygiene/test_review_checks.py [-v]
"""
import os, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)
import review_checks as rc  # noqa: E402

ENV = {k: v for k, v in os.environ.items() if not k.startswith("GIT_") and k != "HYGIENE_BASE"}
ENV.update({"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid", "GIT_COMMITTER_NAME": "t",
            "GIT_COMMITTER_EMAIL": "t@example.invalid", "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"})

WORKFLOW = "jobs:\n  b:\n    steps:\n      - run: lake build {targets}\n"
BASE = {
    ".github/workflows/lean.yml": WORKFLOW.format(targets="Solidity solidity-lean"),
    "Solidity.lean": "import Solidity.A\nimport Solidity.B\n",
    "Solidity/A.lean": "/- doc -/\nimport Solidity.C\n\ndef a := 1\nimport Solidity.Late\n",
    "Solidity/B.lean": "def b := 2\n",
    "Solidity/C.lean": "def c := 3\n",
    "Solidity/Late.lean": "def late := 4\n",
    "scripts/AxiomAudit.lean": "import Solidity\n",
    "scripts/x.test.mjs": "test('a', () => {});\n",
    "scripts/test_y.py": "class T:\n    def test_a(self): pass\n",
}


class Repo:
    def __init__(self):
        self.tmp = tempfile.TemporaryDirectory(); self.dir = self.tmp.name
        self.git("init", "-q", "-b", "master")
        self.base = self.commit(BASE, "base")

    def git(self, *a):
        return subprocess.run(["git", *a], cwd=self.dir, env=ENV, capture_output=True, text=True, check=True).stdout

    def commit(self, files, msg, delete=()):
        for p, t in files.items():
            os.makedirs(os.path.dirname(os.path.join(self.dir, p)) or self.dir, exist_ok=True)
            with open(os.path.join(self.dir, p), "w") as f: f.write(t)
        for p in delete: self.git("rm", "-q", p)
        self.git("add", "-A"); self.git("commit", "-q", "--allow-empty", "-m", msg)
        return self.git("rev-parse", "HEAD").strip()

    def check(self, head):
        old = os.getcwd(); os.chdir(self.dir)
        try: return rc.run(self.base, head)
        finally: os.chdir(old)


class Imports(unittest.TestCase):
    def test_header_only(self):
        self.assertEqual(rc.imports(BASE["Solidity/A.lean"]), ["Solidity.C"])

    def test_several_modules_per_line_and_continuation(self):
        self.assertEqual(rc.imports("import A B\n  C.D\nimport E -- note\ndef x := 1\n  F"), ["A", "B", "C.D", "E"])

    def test_inline_and_nested_comments(self):
        self.assertEqual(rc.imports("/- a /- nested -/ still -/\nimport Solidity.A /- why -/ Solidity.B\n-- x\nimport C\nnoncomputable section"),
                         ["Solidity.A", "Solidity.B", "C"])

    def test_module_system_prefixes(self):
        self.assertEqual(rc.imports("module\n") , [])
        self.assertEqual(rc.imports("-- c\npublic import A.B\nmeta import all C\n/- x\n-/\nimport D\ndef x := 1"),
                         ["A.B", "C", "D"])


class Coverage(unittest.TestCase):
    def setUp(self): self.r = Repo(); self.addCleanup(self.r.tmp.cleanup)

    def test_unchanged_passes(self):
        ok, rep = self.r.check(self.r.commit({}, "noop")); self.assertTrue(ok, rep)

    def test_split_root_not_built_fails_both(self):
        h = self.r.commit({"Solidity.lean": "import Solidity.A\n", "SolidityControls.lean": "import Solidity.B\n"}, "split")
        ok, rep = self.r.check(h)
        self.assertFalse(ok)
        self.assertTrue(any("CI build" in l and "Solidity.B" in l for l in rep), rep)
        self.assertTrue(any("axiom audit" in l for l in rep), rep)

    def test_split_root_built_and_audited_passes(self):
        h = self.r.commit({"Solidity.lean": "import Solidity.A\n", "SolidityControls.lean": "import Solidity.B\n",
                           ".github/workflows/lean.yml": WORKFLOW.format(targets="Solidity SolidityControls"),
                           "scripts/AxiomAudit.lean": "import Solidity\nimport SolidityControls\n"},
                          "split\n\nReview-Check: coverage build the new root")
        ok, rep = self.r.check(h); self.assertTrue(ok, rep)
        old = os.getcwd(); os.chdir(self.r.dir)
        try: self.assertEqual([l for l in rc.check_coverage(self.r.base, h) if "no longer reached" in l], [])
        finally: os.chdir(old)

    def test_commented_out_build_fails(self):
        h = self.r.commit({".github/workflows/lean.yml": "jobs:\n  b:\n    steps:\n      # - run: lake build Solidity\n"
                           "      - run: lake env lean x.lean # was: lake build Solidity\n"}, "comment out")
        ok, rep = self.r.check(h)
        self.assertTrue(ok is False and any("workflow line" in l for l in rep), rep)

    def test_build_named_but_not_run_fails(self):
        h = self.r.commit({".github/workflows/lean.yml": "jobs:\n  b:\n    steps:\n      - name: lake build Solidity\n"
                           "        run: echo disabled\n"}, "rename step")
        self.assertFalse(self.r.check(h)[0])

    def test_echoed_or_env_build_fails(self):
        for wf in ("jobs:\n  b:\n    steps:\n      - run: echo lake build Solidity solidity-lean\n",
                   "jobs:\n  b:\n    steps:\n      - run: |\n          echo off\n        env:\n          N: lake build Solidity\n"):
            h = self.r.commit({".github/workflows/lean.yml": wf}, "evade")
            self.assertFalse(self.r.check(h)[0], wf)

    def test_build_edit_with_trailer_passes(self):
        h = self.r.commit({".github/workflows/lean.yml": "jobs:\n  b:\n    steps:\n      - run: 'lake build Solidity'\n"},
                          "quote\n\nReview-Check: coverage quoting only")
        ok, rep = self.r.check(h); self.assertTrue(ok, rep)

    def test_unrelated_workflow_edit_passes(self):
        h = self.r.commit({".github/workflows/lean.yml": BASE[".github/workflows/lean.yml"] + "      - run: echo done\n"}, "more")
        ok, rep = self.r.check(h); self.assertTrue(ok, rep)

    def test_imports_joined_on_one_line_pass(self):
        h = self.r.commit({"Solidity.lean": "import Solidity.A Solidity.B\n"}, "join")
        ok, rep = self.r.check(h); self.assertTrue(ok, rep)

    def test_import_on_second_name_dropped_fails(self):
        self.r.base = self.r.commit({"Solidity.lean": "import Solidity.A Solidity.B\n"}, "join")
        h = self.r.commit({"Solidity.lean": "import Solidity.A\n"}, "drop")
        self.assertFalse(self.r.check(h)[0])

    def test_audit_only_loss(self):
        h = self.r.commit({"scripts/AxiomAudit.lean": "import Solidity.A\n"}, "narrow audit")
        ok, rep = self.r.check(h)
        self.assertFalse(ok); self.assertTrue(any("axiom audit" in l for l in rep) and not any("CI build" in l for l in rep), rep)

    def test_deleting_a_module_passes(self):
        h = self.r.commit({"Solidity.lean": "import Solidity.A\n"}, "delete B", delete=["Solidity/B.lean"])
        ok, rep = self.r.check(h); self.assertTrue(ok, rep)

    def test_trailer_waives(self):
        h = self.r.commit({"Solidity.lean": "import Solidity.A\n"}, "drop B\n\nReview-Check: coverage B is opt-in now")
        ok, rep = self.r.check(h)
        self.assertTrue(ok, rep); self.assertTrue(any(l.startswith("waived coverage") for l in rep), rep)

    def test_trailer_for_other_rule_does_not_waive(self):
        h = self.r.commit({"Solidity.lean": "import Solidity.A\n"}, "drop B\n\nReview-Check: tests something")
        self.assertFalse(self.r.check(h)[0])

    def test_example_in_body_is_not_a_trailer(self):
        h = self.r.commit({"Solidity.lean": "import Solidity.A\n"},
                          "drop B\n\nExample:\nReview-Check: coverage looks like this\n\nOrdinary prose ends the message.")
        self.assertFalse(self.r.check(h)[0])

    def test_trailer_needs_a_reason(self):
        h = self.r.commit({"Solidity.lean": "import Solidity.A\n"}, "drop B\n\nReview-Check: coverage")
        self.assertFalse(self.r.check(h)[0])


class Tests(unittest.TestCase):
    def setUp(self): self.r = Repo(); self.addCleanup(self.r.tmp.cleanup)

    def test_todo_in_existing_js_test_fails(self):
        h = self.r.commit({"scripts/x.test.mjs": "test('a', {todo: 'later'}, () => {});\n"}, "todo")
        ok, rep = self.r.check(h)
        self.assertFalse(ok); self.assertTrue(any("scripts/x.test.mjs" in l for l in rep), rep)

    def test_python_skip_fails(self):
        h = self.r.commit({"scripts/test_y.py": "import unittest\nclass T:\n    @unittest.skip('x')\n    def test_a(self): pass\n"}, "skip")
        self.assertFalse(self.r.check(h)[0])

    def test_guarded_skiptest_passes(self):
        h = self.r.commit({"scripts/test_y.py": "class T:\n    def test_a(self):\n        if NO: self.skipTest('platform')\n"}, "guard")
        ok, rep = self.r.check(h); self.assertTrue(ok, rep)

    def test_moving_a_marker_passes(self):
        b = self.r.commit({"scripts/x.test.mjs": "test.skip('a', () => {});\ntest('b', () => {});\n"}, "skip a\n\nReview-Check: tests seed")
        self.r.base = b
        h = self.r.commit({"scripts/x.test.mjs": "test('a', () => {});\ntest.skip('b', () => {});\n"}, "move")
        ok, rep = self.r.check(h); self.assertTrue(ok, rep)

    def test_second_marker_on_a_line_fails(self):
        self.r.base = self.r.commit({"scripts/x.test.mjs": "test.skip('a', f); test('b', f);\n"}, "s\n\nReview-Check: tests seed")
        h = self.r.commit({"scripts/x.test.mjs": "test.skip('a', f); test.skip('b', f);\n"}, "more")
        self.assertFalse(self.r.check(h)[0])

    def test_renamed_test_with_new_marker_fails(self):
        body = "".join(f"test('t{i}', () => {{ check({i}); }});\n" for i in range(12))
        self.r.base = self.r.commit({"scripts/x.test.mjs": body}, "grow")
        h = self.r.commit({"scripts/w.test.mjs": body + "test.todo('a', () => {});\n"}, "rename",
                          delete=["scripts/x.test.mjs"])
        self.assertFalse(self.r.check(h)[0])

    def test_renamed_to_non_test_name_with_new_marker_fails(self):
        body = "".join(f"test('t{i}', () => {{ check({i}); }});\n" for i in range(12))
        self.r.base = self.r.commit({"scripts/x.test.mjs": body}, "grow")
        h = self.r.commit({"scripts/x.mjs": body + "test.skip('a', () => {});\n"}, "rename",
                          delete=["scripts/x.test.mjs"])
        self.assertFalse(self.r.check(h)[0])

    def test_new_test_file_passes(self):
        h = self.r.commit({"scripts/z.test.mjs": "test.todo('later');\n"}, "new")
        ok, rep = self.r.check(h); self.assertTrue(ok, rep)

    def test_non_test_file_ignored(self):
        h = self.r.commit({"scripts/tool.mjs": "const o = {todo: 1};\n"}, "tool")
        ok, rep = self.r.check(h); self.assertTrue(ok, rep)

    def test_trailer_waives(self):
        h = self.r.commit({"scripts/x.test.mjs": "test.todo('a');\n"}, "todo\n\nReview-Check: tests decided in H1")
        self.assertTrue(self.r.check(h)[0])


if __name__ == "__main__":
    unittest.main()
