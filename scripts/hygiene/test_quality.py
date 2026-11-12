#!/usr/bin/env python3
"""Tests for scripts/hygiene/quality.py: the counts on small inputs, the regex `clean` against
reach.py's own, the baseline rules, and the ratchet on temporary Git repositories (counts that
need reach.py's census or ruff are given by stubs there, so the tests run in seconds).

Usage: python3 -B scripts/hygiene/test_quality.py [-v]
"""
import json, os, random, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)
import quality as q  # noqa: E402

ENV = {k: v for k, v in os.environ.items() if not k.startswith("GIT_") and k != "HYGIENE_BASE"}
ENV.update({"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid", "GIT_COMMITTER_NAME": "t",
            "GIT_COMMITTER_EMAIL": "t@example.invalid", "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"})


class Clean(unittest.TestCase):
    """fast_clean must equal reach.py's clean character for character."""

    def test_reach_clean_is_replaced_by_the_fast_one(self):
        self.assertIs(q.reach_module().clean.__wrapped__, q.fast_clean)

    def test_against_reach_clean(self):
        ref = original_clean()
        cases = ['"a\\', '/- /- -/', '"\\\n"x', '--x', 'a"b\\"c"d', '/-/', '-/"', '/--/ x', '"--"', '/- "-/" -/',
                 '-- /-\nx', 'a /- b\n c -/ d', '"unterminated\nline', '/- open', '"\\', '\\"', 'x -- "y\nz"']
        for t in cases: self.assertEqual(q.fast_clean(t), ref(t), repr(t))
        rnd = random.Random(7)
        alphabet = ['/', '-', '"', '\\', '\n', 'a', ' ', 'λ']
        for _ in range(3000):
            t = "".join(rnd.choice(alphabet) for _ in range(rnd.randint(0, 24)))
            self.assertEqual(q.fast_clean(t), ref(t), repr(t))


def original_clean():
    """reach.py's own clean, from a fresh import (the quality module swaps it out)."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("reach_ref", os.path.join(
        HERE, "..", "..", "docs/audits/direction-tools/reachability/reach.py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod.clean


def lean_theorem(name, body_lines):
    return f"theorem {name} : True := by\n" + "".join("  trivial\n" for _ in range(body_lines - 1))


class Counts(unittest.TestCase):
    def test_nlines(self):
        self.assertEqual([q.nlines(s) for s in ("", "a", "a\n", "a\nb", "a\n\n")], [0, 1, 1, 2, 2])

    def test_long_files(self):
        texts = {"A.lean": "x\n" * 1500, "B.lean": "x\n" * 1501}
        self.assertEqual(q.long_files(texts), [("B.lean", 1501)])

    def test_proof_spans_end_at_the_next_declaration(self):
        text = "namespace N\n" + lean_theorem("big", 151) + lean_theorem("small", 150) + "end N\n"
        spans = {name: n for _, name, _, n in q.proof_spans(text)}
        self.assertEqual(spans, {"big": 151, "small": 150})
        self.assertEqual([r[2] for r in q.long_proofs({"F.lean": text})], ["big"])

    def test_examples_and_lemmas_count_defs_do_not(self):
        body = "".join("  trivial\n" for _ in range(160))
        text = ("example : True := by\n" + body + "lemma l : True := by\n" + body
                + "def d : Nat :=\n" + "".join("  0 +\n" for _ in range(160)) + "  0\n")
        self.assertEqual(sorted(r[1] for r in q.long_proofs({"F.lean": text})), ["example", "lemma"])

    def test_comment_lines_are_not_declarations(self):
        text = lean_theorem("t", 151).replace("  trivial\n", "  -- theorem fake : True\n  trivial\n", 1)
        self.assertEqual(len(q.long_proofs({"F.lean": text})), 1)

    def test_duplicate_windows(self):
        block = "".join(f"line {i} = {i} + 1\n" for i in range(40))
        self.assertEqual(q.duplicate_windows({"a.py": block})[0], 0)
        # A 40-line copy repeats 11 windows of 30 lines; spacing and comment-only lines do not matter.
        copy = block.replace(" = ", "=").replace("\n", "\n    # note\n", 3)
        n, per = q.duplicate_windows({"a.py": block, "b.py": "x = 0\n" + copy})
        self.assertEqual(n, 11); self.assertEqual(per, {"b.py": 11})
        # Two copies: 22 repeated windows.
        self.assertEqual(q.duplicate_windows({"a.py": block, "b.py": block, "c.py": block})[0], 22)

    def test_duplicate_windows_skip_blank_and_lean_comment_lines(self):
        block = "".join(f"def f{i} := {i}\n" for i in range(30))
        spaced = "".join(f"def f{i} := {i}\n\n-- c{i}\n" for i in range(30))
        self.assertEqual(q.duplicate_windows({"A.lean": block, "B.lean": spaced})[0], 1)

    def test_code_paths(self):
        t = {p: "0" for p in ("Solidity/A.lean", "scripts/x.py", "scripts/y.json", "docs/z.py",
                              "Solidity/vendor/V.lean", "scripts/n/node_modules/m.js", "scripts/s.sh")}
        self.assertEqual(q.code_paths(t), ["Solidity/A.lean", "scripts/s.sh", "scripts/x.py"])

    def test_lean_warnings_are_distinct_locations(self):
        with tempfile.NamedTemporaryFile("w", suffix=".log", delete=False) as f:
            f.write("✔ [1/3] Built A\nwarning: ./A.lean:3:4: unused variable `h`\n"
                    "warning: ./A.lean:3:4: unused variable `h`\nwarning: ./B.lean:9:0: declaration uses 'sorry'\n"
                    "error: ./C.lean:1:1: boom\n")
        try:
            self.assertEqual(q.lean_warnings(f.name)[0], 2)
        finally:
            os.unlink(f.name)


def baseline(**metrics):
    m = {k: 0 for k in q.METRICS}; m.update(metrics)
    return {"seed": "0" * 40, "python_dead_code_tool": "ruff 1", "metrics": m}


class Baseline(unittest.TestCase):
    def test_parse_rejects_bad_shapes(self):
        good = baseline()
        q.parse_baseline(json.dumps(good), "t")
        for bad in ({**good, "extra": 1}, {**good, "metrics": {**good["metrics"], "x": 1}},
                    {**good, "metrics": {**good["metrics"], "long_proofs": -1}},
                    {**good, "metrics": {**good["metrics"], "long_proofs": True}}, {**good, "seed": "abc"}):
            with self.assertRaises(q.SetupError): q.parse_baseline(json.dumps(bad), "t")

    def test_history(self):
        base = baseline(long_proofs=5, lean_warnings=None)
        self.assertEqual(q.baseline_history(base, baseline(long_proofs=4, lean_warnings=None), "w"), [])
        self.assertEqual(q.baseline_history(base, baseline(long_proofs=5, lean_warnings=7), "w"), [])
        self.assertIn("rises", q.baseline_history(base, baseline(long_proofs=6), "w")[0])
        self.assertIn("null", q.baseline_history(base, baseline(long_proofs=None), "w")[0])
        self.assertIn("missing", q.baseline_history(base, None, "w")[0])
        self.assertEqual(q.baseline_history(None, baseline(long_proofs=99), "w"), [])
        tool = baseline(); tool["python_dead_code_tool"] = "ruff 2"
        self.assertIn("python_dead_code_tool", q.baseline_history(base, tool, "w")[0])


class Repo:
    def __init__(self, d): self.d = d

    def git(self, *a):
        r = subprocess.run(["git", *a], cwd=self.d, env=ENV, capture_output=True, text=True)
        if r.returncode: raise AssertionError(f"git {a}: {r.stderr}")
        return r.stdout.strip()

    def commit(self, files, msg="c"):
        for p, data in files.items():
            full = os.path.join(self.d, p); os.makedirs(os.path.dirname(full), exist_ok=True)
            if data is None: os.unlink(full)
            else:
                with open(full, "w") as f: f.write(data if isinstance(data, str) else json.dumps(data, indent=1))
        self.git("add", "-A"); self.git("commit", "-q", "--allow-empty", "-m", msg)
        return self.git("rev-parse", "HEAD")


class Ratchet(unittest.TestCase):
    """quality.evaluate on real commits; census and ruff counts come from a stub table."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.repo = Repo(self.tmp.name)
        self.repo.git("init", "-q"); self.cwd = os.getcwd(); os.chdir(self.tmp.name)
        self.stub = {}
        self.saved = (q.unreachable_declarations, q.ruff_version, q.python_dead_code, q.cache_dir)
        q.unreachable_declarations = lambda c: self.stub.get(c, {}).get("unreachable", 0)
        q.ruff_version = lambda: "ruff 1"
        q.python_dead_code = lambda c, t: (self.stub.get(c, {}).get("ruff", 0), [])
        q.cache_dir = lambda: None

    def tearDown(self):
        q.unreachable_declarations, q.ruff_version, q.python_dead_code, q.cache_dir = self.saved
        os.chdir(self.cwd); self.tmp.cleanup()

    def run_eval(self, base, head, only=q.METRICS):
        return q.evaluate(base, head, only, None, False)

    def base_commit(self, b=None, files=None):
        files = {"Solidity/A.lean": lean_theorem("a", 10), **(files or {})}
        files[q.BASELINE] = b or baseline(lean_warnings=None)
        return self.repo.commit(files)

    def test_unchanged_passes(self):
        base = self.base_commit()
        head = self.repo.commit({"README": "x"})
        ok, rep = self.run_eval(base, head)
        self.assertTrue(ok, rep)
        self.assertTrue(any("inputs unchanged from base" in r for r in rep), rep)

    def test_new_long_proof_fails_and_names_it(self):
        base = self.base_commit()
        head = self.repo.commit({"Solidity/B.lean": lean_theorem("big", 200)})
        ok, rep = self.run_eval(base, head, ("long_proofs",))
        self.assertFalse(ok)
        self.assertIn("FAIL long_proofs: 1, over the baseline 0", rep[0])
        self.assertIn("Solidity/B.lean:1 theorem big (200 lines)", "\n".join(rep))

    def test_removing_one_offender_while_adding_another_is_level(self):
        base = self.base_commit(baseline(long_proofs=1, lean_warnings=None), {"Solidity/B.lean": lean_theorem("big", 200)})
        head = self.repo.commit({"Solidity/B.lean": None, "Solidity/C.lean": lean_theorem("other", 300)})
        self.assertTrue(self.run_eval(base, head, ("long_proofs",))[0])

    def test_stale_baseline_passes_a_lane_that_adds_nothing(self):
        # The baseline says 0 but base already has one long file (it landed before a refresh).
        base = self.base_commit(files={"Solidity/L.lean": "x\n" * 1600})
        head = self.repo.commit({"Solidity/M.lean": "y\n"})
        ok, rep = self.run_eval(base, head, ("lean_long_files",))
        self.assertTrue(ok, rep); self.assertIn("stale", rep[0])
        head2 = self.repo.commit({"Solidity/N.lean": "z\n" * 1600})
        ok, rep = self.run_eval(base, head2, ("lean_long_files",))
        self.assertFalse(ok); self.assertIn("over base's 1", rep[0])

    def test_baseline_may_not_rise(self):
        base = self.base_commit()
        head = self.repo.commit({q.BASELINE: baseline(duplicate_windows=3, lean_warnings=None)})
        ok, rep = self.run_eval(base, head)
        self.assertFalse(ok); self.assertIn("rises from 0 to 3", rep[0])

    def test_missing_baseline_fails(self):
        base = self.base_commit()
        head = self.repo.commit({q.BASELINE: None})
        ok, rep = self.run_eval(base, head)
        self.assertFalse(ok); self.assertIn("missing", rep[0])

    def test_census_and_ruff_counts(self):
        base = self.base_commit(baseline(unreachable_declarations=5, python_dead_code=2, lean_warnings=None))
        head = self.repo.commit({"Solidity/B.lean": "def b := 1\n", "scripts/x.py": "import os\n"})
        self.stub[head] = {"unreachable": 6, "ruff": 2}; self.stub[base] = {"unreachable": 5, "ruff": 2}
        ok, rep = self.run_eval(base, head, ("unreachable_declarations", "python_dead_code"))
        self.assertFalse(ok); self.assertIn("FAIL unreachable_declarations: 6, over the baseline 5 (base 5)", rep[0])
        self.stub[head] = {"unreachable": 4, "ruff": 3}
        ok, rep = self.run_eval(base, head, ("unreachable_declarations", "python_dead_code"))
        self.assertFalse(ok); self.assertIn("FAIL python_dead_code: 3", rep[0])

    def test_other_ruff_version_is_skipped_with_a_note(self):
        base = self.base_commit()
        head = self.repo.commit({"scripts/x.py": "import os\n"})
        self.stub[head] = {"ruff": 9}
        q.ruff_version = lambda: "ruff 2"
        ok, rep = self.run_eval(base, head, ("python_dead_code",))
        self.assertTrue(ok, rep); self.assertIn("baseline counted with ruff 1, this host has ruff 2", rep[0])
        q.ruff_version = lambda: None
        ok, rep = self.run_eval(base, head, ("python_dead_code",))
        self.assertTrue(ok, rep); self.assertIn("ruff is not installed", rep[0])

    def test_lean_warnings_null_is_reported_not_enforced(self):
        base = self.base_commit()
        ok, rep = self.run_eval(base, self.repo.commit({}), ("lean_warnings",))
        self.assertTrue(ok, rep); self.assertIn("no --lean-log", rep[0])


class Committed(unittest.TestCase):
    def test_committed_baseline_parses(self):
        with open(os.path.join(HERE, "baseline.json"), "rb") as f:
            b = q.parse_baseline(f.read(), "working tree")
        self.assertIsNone(b["metrics"]["lean_warnings"])
        self.assertTrue(all(isinstance(b["metrics"][k], int) for k in q.METRICS if k != "lean_warnings"))


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], *sys.argv[1:]])
