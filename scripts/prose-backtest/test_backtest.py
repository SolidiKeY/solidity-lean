"""Tiny-history tests for backtest.py with independently expected counts."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from fractions import Fraction

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import backtest as bt  # noqa: E402

CHECKER = (HERE.parent / "check-prose-budget").read_bytes()
CHECKER_BLOB = bt.git_blob_id(CHECKER)
DAY = 86400
T0 = 1_800_000_000


class History:
    def __init__(self, root):
        self.root = Path(root)
        self.root.mkdir(parents=True)
        self.git("init", "-q", "-b", "master")
        self.git("config", "user.email", "t@example.invalid")
        self.git("config", "user.name", "t")
        self.git("config", "commit.gpgsign", "false")

    def git(self, *args, env=None):
        return subprocess.run(["git", "-C", str(self.root), *args], check=True, env=env,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout.decode().strip()

    def commit(self, ts, files, remove=()):
        for path, text in files.items():
            target = self.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(text if isinstance(text, bytes) else text.encode())
        for path in remove:
            (self.root / path).unlink()
        self.git("add", "-A")
        env = dict(os.environ, GIT_AUTHOR_DATE=f"@{ts} +0000", GIT_COMMITTER_DATE=f"@{ts} +0000")
        self.git("commit", "-q", "--allow-empty", "-m", f"c{ts}", env=env)
        return self.git("rev-parse", "HEAD")


def lean(code_lines, comment_lines=0, doc_lines=0):
    out = ["/-- " + "doc " * 1] + ["doc"] * (doc_lines - 2) + ["-/"] if doc_lines >= 2 else []
    out += ["-- c"] * comment_lines
    out += [f"def x{i} := {i}" for i in range(code_lines)]
    return "\n".join(out) + "\n"


def base_files(baseline=None, checker=True):
    files = {"docs/guide/a.md": "one\ntwo\n", "Solidity/Core/A.lean": lean(10, 2)}
    if checker:
        files["scripts/check-prose-budget"] = CHECKER
    if baseline is not None:
        files["scripts/prose-baseline.json"] = json.dumps(baseline)
    return files


class Scanner(unittest.TestCase):
    def lines(self, text):
        scanner, spans, code = bt.lean_lines(text)
        return scanner.comments, scanner.docs, code

    def test_mixed_comment_and_code(self):
        comments, docs, code = self.lines("def a := 1 -- note\n-- only\n  \ndef b := 2\n")
        self.assertEqual(comments, {1, 2})
        self.assertEqual(code, {1, 4})
        self.assertEqual(docs, set())

    def test_nested_comments_and_strings(self):
        text = ('/- outer /- inner -/ still\n'      # 1 comment only
                'outer -/ def c := "a -- b \\" /-"\n'  # 2 comment + code, string hides tokens
                'def d := «x -- y»\n'               # 3 code only (quoted identifier)
                'def e := \'"\' -- tail\n')          # 4 code + comment (char literal)
        comments, docs, code = self.lines(text)
        self.assertEqual(comments, {1, 2, 4})
        self.assertEqual(code, {2, 3, 4})

    def test_docstrings_overlap_comments(self):
        comments, docs, code = self.lines("/-- doc\nline -/\ndef f := 1\n/-! mod -/\n")
        self.assertEqual(docs, {1, 2, 4})
        self.assertEqual(comments, {1, 2, 4})
        self.assertTrue(docs <= comments)
        self.assertEqual(code, {3})

    def test_comment_spans_stripped_not_whole_lines(self):
        comments, _, code = self.lines("/- a -/ def g := /- b -/ 2 /- c\n-/\n")
        self.assertEqual(comments, {1, 2})
        self.assertEqual(code, {1})

    def test_rational_limit_is_exact(self):
        cal = {"numerator": 1, "denominator": 10}
        m = Fraction(1, 20)
        self.assertTrue(bt.ratio_limit_ok(21, 200, cal, m)[0])   # 21/200 == 1.05/10
        self.assertFalse(bt.ratio_limit_ok(22, 200, cal, m)[0])
        self.assertEqual(bt.limit_value(200, cal, m), 21)
        self.assertFalse(bt.ratio_limit_ok(1, 0, cal, m)[0])
        self.assertTrue(bt.ratio_limit_ok(0, 0, cal, m)[0])
        self.assertFalse(bt.ratio_limit_ok(1, 5, {"numerator": 3, "denominator": 0}, m)[0])
        self.assertFalse(bt.ratio_limit_ok(1, 5, {"numerator": 0, "denominator": 9}, m)[0])


class GitCase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.h = History(Path(self.tmp.name) / "r")
        self.out = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def calibrate(self, commit, **extra):
        path = self.out / "estimate.json"
        argv = ["--mode", "calibrate", "--repo", str(self.h.root), "--calibration", commit,
                "--margin", "1/10", "--sensitivity", "0,1/10",
                "--versions", json.dumps({CHECKER_BLOB: "v3"}), "--output", str(path)]
        for key, value in extra.items():
            argv += ["--" + key.replace("_", "-"), value]
        self.assertEqual(bt.main(argv), 0)
        return path

    def replay(self, end, estimate, days=30):
        path = self.out / "replay.json"
        with contextlib.redirect_stdout(io.StringIO()):
            bt.main(["--repo", str(self.h.root), "--end", end, "--days", str(days),
                     "--estimate", str(estimate), "--output", str(path)])
        return json.loads(path.read_text())


class Interval(GitCase):
    def test_exact_boundary_predecessor_and_first_parent(self):
        c0 = self.h.commit(T0, base_files())
        c1 = self.h.commit(T0 + DAY - 1, {"x": "1"})
        c2 = self.h.commit(T0 + DAY, {"x": "2"})          # exactly start: included
        self.h.git("checkout", "-q", "-b", "side", c1)
        side = self.h.commit(T0 + DAY + 50, {"y": "1"})
        self.h.git("checkout", "-q", "master")
        env = dict(os.environ, GIT_AUTHOR_DATE=f"@{T0 + DAY + 100} +0000",
                   GIT_COMMITTER_DATE=f"@{T0 + DAY + 100} +0000")
        self.h.git("merge", "-q", "--no-ff", "-m", "merge", "side", env=env)
        merge = self.h.git("rev-parse", "HEAD")
        end = self.h.commit(T0 + 3 * DAY, {"x": "3"})
        frozen = bt.freeze_interval(bt.Repo(self.h.root), end, 2)
        self.assertEqual(frozen["start_ts"], T0 + DAY)
        self.assertEqual(frozen["first_parent_commits"], [c2, merge, end])
        self.assertNotIn(side, frozen["first_parent_commits"])
        self.assertEqual(frozen["predecessor"], c1)
        self.assertFalse(frozen["history_incomplete"])
        all_fp = self.h.git("rev-list", "--first-parent", end).split()
        self.assertEqual(len(all_fp), frozen["first_parent_ancestors_total"])
        self.assertIn(c0, all_fp)

    def test_root_reached_is_reported_and_late_stamp_kept_out(self):
        c0 = self.h.commit(T0, base_files())
        late = self.h.commit(T0 + 10 * DAY, {"x": "1"})   # stamped after the end commit
        end = self.h.commit(T0 + 5 * DAY, {"x": "2"})
        frozen = bt.freeze_interval(bt.Repo(self.h.root), end, 30)
        self.assertTrue(frozen["history_incomplete"])
        self.assertIsNone(frozen["predecessor"])
        self.assertEqual(frozen["selected_outside_interval"], [late])
        self.assertEqual(frozen["first_parent_commits"], [c0, end])


class Measure(GitCase):
    def test_generated_excluded_both_sides_and_unknown_kept(self):
        gen = "/-! Generated by scripts/gen.py; do not edit. -/\ndef g := 1\ndef h := 2\n"
        claimed = "/-! Generated by scripts/missing.py. -/\ndef k := 1\n"
        block = ("def a := 1\n-- BEGIN generated by scripts/gen.py\n-- G1 note\ndef b := 2\n"
                 "-- END generated by scripts/gen.py\ndef c := 3 -- G2\n")
        c = self.h.commit(T0, {"scripts/gen.py": "print()\n", "Solidity/Core/Gen.lean": gen,
                               "Solidity/Core/Claim.lean": claimed, "Solidity/Core/Blk.lean": block,
                               "docs/x.md": "<!-- Generated by scripts/gen.py -->\nbody\n",
                               "docs/y.md": "head\n<!-- BEGIN generated by scripts/gen.py -->\nz\n"
                                            "<!-- END generated by scripts/gen.py -->\n"})
        repo = bt.Repo(self.h.root)
        m = bt.measure_commit(repo, bt.Analyzer(repo), c, None)
        core = m["normalized"]["Solidity/Core"]
        # Claim.lean: 1 comment line, 1 code line; Blk.lean outside block: 1 comment, 2 code
        self.assertEqual(core["comment_lines"], 1 + 1)
        self.assertEqual(m["code"]["Solidity/Core"], 1 + 2)
        self.assertEqual(core["process_ids"], 1)            # G2 kept, G1 inside block dropped
        self.assertEqual(m["legacy"]["Solidity/Core"]["comment_lines"], 1 + 1 + 4)
        self.assertEqual(m["normalized"]["docs/_root"]["docs_lines"], 1)   # y.md head only
        self.assertEqual(m["legacy"]["docs/_root"]["docs_lines"], 6)
        paths = {(e["path"], e["rule"]) for e in m["exclusions"]}
        self.assertIn(("Solidity/Core/Gen.lean", "header"), paths)
        self.assertIn(("docs/x.md", "header"), paths)
        self.assertEqual([u["path"] for u in m["unknown"]], ["Solidity/Core/Claim.lean"])

    def test_process_ids_use_registered_roots(self):
        src = "import Solidity.G7.Mod\n-- H3 and G4\ndef q := 1\n"
        c = self.h.commit(T0, {"Solidity.lean": "import Solidity.G7.Mod\n",
                               "Solidity/Core/P.lean": src, "docs/a.md": "a\n"})
        repo = bt.Repo(self.h.root)
        m = bt.measure_commit(repo, bt.Analyzer(repo), c, None)
        self.assertEqual(m["legacy"]["Solidity/Core"]["process_ids"], 2)
        self.assertEqual(m["legacy_v1_process_ids"]["Solidity/Core"], 3)
        c2 = self.h.commit(T0 + 1, {"Solidity.lean": "import Solidity.Other\n"})
        m2 = bt.measure_commit(repo, bt.Analyzer(repo), c2, None)
        self.assertEqual(m2["legacy"]["Solidity/Core"]["process_ids"], 3)

    def test_exempt_import_in_generated_block_not_subtracted_twice(self):
        src = ("-- BEGIN generated by scripts/gen.py\nimport Solidity.G7.Mod -- trailing\n"
               "-- END generated by scripts/gen.py\n-- H3 kept\ndef q := 1\n")
        c = self.h.commit(T0, {"scripts/gen.py": "print()\n", "Solidity.lean": "import Solidity.G7.Mod\n",
                               "Solidity/Core/P.lean": src, "docs/a.md": "a\n"})
        repo = bt.Repo(self.h.root)
        m = bt.measure_commit(repo, bt.Analyzer(repo), c, None)
        self.assertEqual(m["legacy"]["Solidity/Core"]["process_ids"], 1)       # G7 exempt, H3 counted
        self.assertEqual(m["normalized"]["Solidity/Core"]["process_ids"], 1)   # not 0 or -1
        c2 = self.h.commit(T0 + 1, {"Solidity.lean": "import Solidity.Other\n"})
        m2 = bt.measure_commit(repo, bt.Analyzer(repo), c2, None)
        self.assertEqual(m2["legacy"]["Solidity/Core"]["process_ids"], 2)
        self.assertEqual(m2["normalized"]["Solidity/Core"]["process_ids"], 1)  # counted G7 removed
        repo.close()

    def test_docs_mapping_repository_denominator(self):
        c = self.h.commit(T0, {"docs/a/x.md": "1\n2\n3\n", "Solidity/A/a.lean": lean(4),
                               "Solidity/B/b.lean": lean(6), "Solidity/B/notes.txt": "x\n"})
        repo = bt.Repo(self.h.root)
        m = bt.measure_commit(repo, bt.Analyzer(repo), c, None)
        self.assertEqual(bt.denominator("docs/a", m["code"], {}), (10, "repository-solidity"))
        self.assertEqual(bt.denominator("Solidity/B", m["code"], {}), (6, "self"))
        self.assertEqual(bt.denominator("docs/a", m["code"], {"docs/a": ["Solidity/A"]}), (4, "Solidity/A"))


class Replay(GitCase):
    def build(self):
        h = self.h
        pre = h.commit(T0, base_files(checker=False))                    # no checker/baseline
        cal = h.commit(T0 + DAY, base_files({"Solidity/Core": {"docs_lines": 0, "comment_lines": 2,
                                                               "docstring_lines": 0, "process_ids": 0},
                                             "docs/guide": {"docs_lines": 2, "comment_lines": 0,
                                                            "docstring_lines": 0, "process_ids": 0}}))
        prose = h.commit(T0 + 2 * DAY, {"Solidity/Core/A.lean": lean(10, 3)})    # prose only
        keep = h.commit(T0 + 3 * DAY, {"docs/guide/a.md": "one\ntwo\n"})        # retains failure
        grow = h.commit(T0 + 4 * DAY, {"Solidity/Core/A.lean": lean(20, 4)})    # proportional
        over = h.commit(T0 + 5 * DAY, {"Solidity/Core/A.lean": lean(30, 9)})    # excessive
        shrink = h.commit(T0 + 6 * DAY, {"Solidity/Core/A.lean": lean(20, 6)})  # code removed
        new = h.commit(T0 + 7 * DAY, {"Solidity/New/N.lean": "-- n\n",           # zero-code new area
                                      "Solidity/Core/A.lean": lean(20, 2)})
        return dict(pre=pre, cal=cal, prose=prose, keep=keep, grow=grow, over=over, shrink=shrink, new=new)

    def test_full_replay_rules_and_failure_index(self):
        c = self.build()
        est = self.calibrate(c["cal"])
        data = json.loads(est.read_text())
        self.assertEqual(data["calibration"]["Solidity/Core"]["comment_lines"],
                         {"numerator": 2, "denominator": 10, "denominator_source": "self",
                          "ratio": "1/5", "null_reason": None})
        self.assertEqual(data["calibration"]["docs/guide"]["docs_lines"]["denominator"], 10)
        out = self.replay(c["new"], est)
        self.assertEqual(out["frozen_inputs"]["first_parent_commits"], list(c.values()))
        commits = {x["commit"]: x for x in out["commits"]}
        self.assertEqual(commits[c["pre"]]["legacy_state"], "checker_or_baseline_absent")
        self.assertEqual(commits[c["cal"]]["position"], "calibration")
        self.assertEqual(commits[c["pre"]]["position"], "before_calibration")

        def fail(rule, commit, area="Solidity/Core", metric="comment_lines"):
            hits = [f for f in out["failure_index"] if (f["rule"], f["commit"], f["area"], f["metric"])
                    == (rule, commit, area, metric)]
            return hits[0] if hits else None

        f = fail("ratio", c["prose"])
        self.assertEqual((f["numerator"], f["denominator"], f["limit"]), (3, 10, 2))
        self.assertIn("prose_rose_without_code", f["causes"])
        self.assertTrue(f["introduced"])
        self.assertTrue(fail("legacy", c["prose"])["introduced"])
        self.assertFalse(fail("ratio", c["keep"])["introduced"])
        self.assertIn("unchanged_counts", fail("ratio", c["keep"])["causes"])
        # 4/20 is exactly the frozen ratio: ratio passes, absolute rules fail
        self.assertIsNone(fail("ratio", c["grow"]))
        self.assertIn("code_rose_with_normal_prose", fail("normalized_absolute", c["grow"])["causes"])
        self.assertIn("code_rose_with_normal_prose", fail("legacy", c["grow"])["causes"])
        over = fail("ratio", c["over"])
        self.assertEqual((over["numerator"], over["denominator"], over["limit"]), (9, 30, 6))
        self.assertIn("code_and_prose_rose", over["causes"])
        shrink = fail("ratio", c["shrink"])
        self.assertIn("denominator_shrank", shrink["causes"])
        self.assertFalse(shrink["introduced"])
        unseen = fail("ratio", c["new"], "Solidity/New")
        self.assertEqual(unseen["reason"], "unseen area: cannot train own allowance")
        self.assertIn("unseen_area", unseen["causes"])
        self.assertEqual((unseen["prior_numerator"], unseen["prior_denominator"]), (0, 0))
        self.assertEqual(fail("legacy", c["prose"])["prior_status"], "pass")
        self.assertNotIn("ratio_exceeded_frozen_allowance", unseen["causes"])
        self.assertIsNone(fail("ratio", c["new"]))   # 2/20 back under
        # exhaustive: every failing in-window row cell appears exactly once
        expected = sum(1 for r in out["rows"] if r["in_window"]
                       for rule in ("legacy", "normalized_absolute", "ratio")
                       if r[rule]["status"] == "fail")
        self.assertEqual(expected, len(out["failure_index"]))
        self.assertEqual(sum(x["fail"]["ratio"] for x in out["commits"]),
                         sum(1 for f in out["failure_index"] if f["rule"] == "ratio"))

    def test_zero_code_area_and_enforcement_exclusion(self):
        h = self.h
        cal = h.commit(T0, base_files() | {"Solidity/Z/Z.lean": "-- only prose\n",
                                          "docs/audits/a.md": "x\n"})
        later = h.commit(T0 + DAY, {"Solidity/Z/Z.lean": "-- only prose\n-- more\n",
                                    "docs/audits/a.md": "x\ny\nz\n"})
        est = self.calibrate(cal, exclude="docs/audits")
        z = json.loads(est.read_text())["calibration"]["Solidity/Z"]["comment_lines"]
        self.assertEqual((z["numerator"], z["denominator"], z["ratio"], z["null_reason"]),
                         (1, 0, None, "zero denominator"))
        out = self.replay(later, est)
        hits = {(f["rule"], f["area"], f["metric"]): f for f in out["failure_index"] if f["commit"] == later}
        zf = hits[("ratio", "Solidity/Z", "comment_lines")]
        self.assertIn("zero_code", zf["causes"])
        audits = hits[("ratio", "docs/audits", "docs_lines")]
        self.assertFalse(audits["enforced_in_proposal"])     # measured, reported, not enforced
        by = out["totals"]["by_rule_and_position"]
        self.assertEqual(by["ratio"]["after_calibration"]["failing_cells"]
                         - by["ratio_enforced"]["after_calibration"]["failing_cells"], 1)

    def test_reintroduced_area_failure_is_introduced_again(self):
        h = self.h
        cal = h.commit(T0, base_files())
        h.commit(T0 + DAY, {"Solidity/New/N.lean": "-- n\n"})
        h.commit(T0 + 2 * DAY, {}, remove=["Solidity/New/N.lean"])
        back = h.commit(T0 + 3 * DAY, {"Solidity/New/N.lean": "-- n\n"})
        out = self.replay(back, self.calibrate(cal))
        f = [x for x in out["failure_index"] if x["commit"] == back and x["rule"] == "ratio"
             and x["area"] == "Solidity/New" and x["metric"] == "comment_lines"][0]
        self.assertTrue(f["introduced"])
        self.assertIsNone(f["prior_status"])

    def test_baseline_evolution_and_absent_area(self):
        h = self.h
        a = h.commit(T0, base_files({"Solidity/Core": dict(docs_lines=0, comment_lines=2,
                                                           docstring_lines=0, process_ids=0)}))
        b = h.commit(T0 + DAY, {"scripts/prose-baseline.json": json.dumps(
            {"Solidity/Core": dict(docs_lines=0, comment_lines=2, docstring_lines=0, process_ids=0),
             "docs/guide": dict(docs_lines=2, comment_lines=0, docstring_lines=0, process_ids=0)})})
        est = self.calibrate(b)
        out = self.replay(b, est)
        legacy = [f for f in out["failure_index"] if f["rule"] == "legacy"]
        self.assertEqual([(f["commit"], f["area"], f["reason"]) for f in legacy],
                         [(a, "docs/guide", "area absent from baseline: zero allowance")])
        blobs = [x["baseline_blob"] for x in out["commits"]]
        self.assertEqual(len(set(blobs)), 2)

    def test_frozen_ratios_invariant_and_replay_deterministic(self):
        c = self.build()
        est = self.calibrate(c["cal"])
        before = est.read_bytes()
        out1 = self.replay(c["new"], est)
        self.assertEqual(est.read_bytes(), before)          # replay never writes the estimate
        self.calibrate(c["cal"])
        self.assertEqual(est.read_bytes(), before)          # later content cannot move ratios
        first = (self.out / "replay.json").read_bytes()
        self.replay(c["new"], est)
        self.assertEqual((self.out / "replay.json").read_bytes(), first)
        self.assertEqual(out1["estimate"]["calibration_commit"], c["cal"])


# ---------------------------------------------------------------- pb2a v2 (additive) controls
# Every expected value below is hand-calculated from the file texts; none is computed
# with backtest.py helpers.

GOALS = "/-- G doc\nline -/\n-- H1 cite\ndef g0 := 0\ndef g1 := 1\ndef g2 := 2\ndef g3 := 3\n"
# Goals: comment lines {1,2,3} = 3, docstring {1,2} = 2, code {4..7} = 4, process IDs H1 = 1


class V2Arithmetic(unittest.TestCase):
    def entry(self, ratio, margin):
        return {"ratio": ratio, "margin": margin, "case": "ratio"}

    def test_noninteger_boundary(self):
        e = self.entry("1/3", "1/2")          # allowance at d = 5: 5/3 + 1/2 = 13/6
        self.assertTrue(bt.v2_test(2, 5, e))  # 2*3*2 = 12 <= 1*5*2 + 1*3 = 13
        self.assertFalse(bt.v2_test(3, 5, e))  # 18 > 13
        self.assertEqual(bt.v2_allowance(5, e), Fraction(13, 6))

    def test_exact_equality_passes(self):
        e = self.entry("1/4", "1/2")          # 10/4 + 1/2 = 3 exactly
        self.assertTrue(bt.v2_test(3, 10, e))
        self.assertFalse(bt.v2_test(4, 10, e))

    def test_zero_ratio_finite_margin_versus_zero_denominator(self):
        z = self.entry("0", "5/2")            # zero ratio: a flat allowance of 5/2 at any d
        for d in (0, 1, 10 ** 9):
            self.assertTrue(bt.v2_test(2, d, z))
            self.assertFalse(bt.v2_test(3, d, z))
        r = self.entry("1/2", "0")            # zero denominator at evaluation: allowance 0
        self.assertTrue(bt.v2_test(0, 0, r))
        self.assertFalse(bt.v2_test(1, 0, r))
        self.assertTrue(bt.v2_test(1, 2, r))

    def test_unmapped_fallback_and_negative_rejected(self):
        self.assertTrue(bt.v2_test(0, 50, None))
        self.assertFalse(bt.v2_test(1, 50, None))
        self.assertEqual(bt.v2_allowance(50, None), 0)
        with self.assertRaises(ValueError):
            bt.v2_test(0, 1, self.entry("-1/2", "0"))

    def test_classification(self):
        self.assertEqual(bt._classify("fail", True), "inherited")
        self.assertEqual(bt._classify("pass", False), "introduced")
        self.assertEqual(bt._classify(None, False), "introduced")
        self.assertEqual(bt._classify("pass", True), "reintroduced")
        self.assertEqual(bt._classify(None, True), "reintroduced")


class V2History(GitCase):
    def build(self):
        h = self.h
        c = {}
        c["pre"] = h.commit(T0 - 1, {"Solidity/Core/A.lean": lean(5, 5), "docs/guide/a.md": "x\n"})
        c["c0"] = h.commit(T0, {"Solidity/Core/A.lean": lean(10, 4), "docs/guide/a.md": "one\ntwo\n",
                                "Solidity/Z/Z.lean": "-- a\n-- b\n", "Solidity/Scratch/S.lean": "-- s\n"})
        c["c1"] = h.commit(T0 + DAY, {"Solidity/Core/A.lean": lean(20, 5),
                                      "Solidity/Scratch/S.lean": "-- s\n-- t\n"})
        c["anchor"] = h.commit(T0 + 2 * DAY, {"Solidity/Core/A.lean": lean(20, 4),
                                              "Solidity/Goals/G.lean": GOALS,
                                              "Solidity/Z/Z.lean": "-- a\n"},
                               remove=["Solidity/Scratch/S.lean"])      # transient area, gone
        c["e1"] = h.commit(T0 + 3 * DAY, {"Solidity/Core/A.lean": lean(40, 10)})        # proportional
        c["e2"] = h.commit(T0 + 4 * DAY, {"Solidity/Core/A.lean": lean(40, 11),          # density
                                          "Solidity/New/N.lean": "def a := 1\n-- n\n",
                                          "docs/guide/a.md": "one\ntwo\n\n\n\n"})          # blank padding
        c["e3"] = h.commit(T0 + 5 * DAY, {"Solidity/Core/A.lean": lean(30, 11),          # code removed
                                          "Solidity/Z/Z.lean": "-- a\n-- b\n-- c\n"})
        c["e4"] = h.commit(T0 + 6 * DAY, {"Solidity/Core/A.lean": lean(30, 8),
                                          "Solidity/Z/Z.lean": "-- a\n-- b\n"})
        c["e5"] = h.commit(T0 + 7 * DAY, {"Solidity/Core/A.lean": lean(30, 9),
                                          "Solidity/Goals/G.lean": GOALS.replace("H1 cite", "H1 cite H2")})
        return c

    def v2_calibrate(self, end, days=2, verified=None, name="policy.json"):
        path = self.out / name
        argv = ["--mode", "v2-calibrate", "--repo", str(self.h.root), "--end", end,
                "--lookback-days", str(days), "--exclude", "docs/guide", "--output", str(path)]
        if verified is not None:
            vpath = self.out / "verified.json"
            vpath.write_text(json.dumps(verified))
            argv += ["--verified", str(vpath)]
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(bt.main(argv), 0)
        return path

    def v2_replay(self, end, policy, days=30, name="v2.json", pb1=None):
        path = self.out / name
        argv = ["--mode", "v2-replay", "--repo", str(self.h.root), "--end", end, "--days", str(days),
                "--policy", str(policy), "--output", str(path)]
        if pb1:
            argv += ["--pb1-replay", str(pb1)]
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(bt.main(argv), 0)
        return json.loads(path.read_text())

    def test_selection_and_coefficients(self):
        c = self.build()
        policy = json.loads(self.v2_calibrate(c["e1"]).read_text())
        sel = policy["specification"]["selection"]
        cover, late = sel["anchors"]
        self.assertEqual((cover["role"], cover["commit"]), ("coverage", c["anchor"]))  # Goals appears
        self.assertEqual(cover["lookback"]["commits"], 3)             # c0, c1, anchor; pre is 1 s early
        self.assertEqual((cover["lookback"]["first"], cover["lookback"]["last"]), (c["c0"], c["anchor"]))
        # Scratch is gone before the coverage anchor: its latest earlier commit anchors it
        self.assertEqual((late["role"], late["commit"], late["areas"]),
                         ("latest_before_coverage", c["c1"], ["Solidity/Scratch"]))
        self.assertEqual(late["lookback"]["commits"], 3)              # pre, c0, c1
        self.assertEqual(policy["coverage"]["status"], "complete")
        self.assertEqual(policy["specification"]["inventory"],
                         ["Solidity/Core", "Solidity/Goals", "Solidity/Z", "docs/guide"])
        self.assertEqual(sel["universe"], ["Solidity/Core", "Solidity/Goals", "Solidity/Scratch",
                                           "Solidity/Z", "docs/guide"])
        self.assertEqual(sel["evaluation_window"]["commits"], 5)      # pre .. e1
        s = policy["calibration"]["Solidity/Scratch"]
        # zero code; present at c0 (1 line) and c1 (2 lines): r = 0, m = 2
        self.assertEqual((s["anchor"], s["metrics"]["comment_lines"]["case"], s["metrics"]["comment_lines"]["margin"],
                          s["metrics"]["comment_lines"]["lookback_commits_with_area"]),
                         (c["c1"], "zero_denominator", "2", 2))
        cal = policy["calibration"]
        core = cal["Solidity/Core"]["metrics"]["comment_lines"]
        # anchor 4/20 = 1/5; residuals c0: 4 - 10/5 = 2, c1: 5 - 20/5 = 1, anchor 0 -> m = 2
        self.assertEqual((core["ratio"], core["margin"], core["case"], core["margin_witness"]),
                         ("1/5", "2", "ratio", c["c0"]))
        self.assertEqual(cal["Solidity/Core"]["metrics"]["docstring_lines"]["case"], "zero_numerator")
        guide = cal["docs/guide"]["metrics"]["docs_lines"]
        # d = all Solidity code = 20 + 4 = 24; r = 2/24 = 1/12; c0: 2 - 10/12 = 7/6, c1: 2 - 20/12 = 1/3
        self.assertEqual((guide["ratio"], guide["margin"], guide["anchor_denominator"]),
                         ("1/12", "7/6", 24))
        self.assertEqual(cal["docs/guide"]["denominator_source"], "repository-solidity")
        goals = cal["Solidity/Goals"]["metrics"]
        self.assertEqual([goals[m]["ratio"] for m in bt.METRICS], ["0", "3/4", "1/2", "1/4"])
        self.assertEqual(goals["comment_lines"]["lookback_commits_with_area"], 1)
        z = cal["Solidity/Z"]["metrics"]["comment_lines"]
        # zero code at the anchor: no ratio invented, margin = largest lookback count (c0: 2)
        self.assertEqual((z["case"], z["ratio"], z["margin"], z["anchor_denominator"]),
                         ("zero_denominator", "0", "2", 0))
        self.assertNotIn("Solidity/New", cal)
        self.assertEqual(policy["specification"]["enforcement_exclusions"], {
            "docs/guide": "H548: measured but outside proposed enforcement until r1"})

    def test_replay_outcomes(self):
        c = self.build()
        policy = self.v2_calibrate(c["e1"])
        before = policy.read_bytes()
        out = self.v2_replay(c["e5"], policy)
        self.assertEqual(policy.read_bytes(), before)
        self.assertEqual(out["policy_sha256_before"], out["policy_sha256_after"])
        self.assertEqual(out["frozen_inputs"]["first_parent_commits"],
                         [c[k] for k in ("pre", "c0", "c1", "anchor", "e1", "e2", "e3", "e4", "e5")])
        pos = {s["commit"]: s["position"] for s in out["commits"]}
        self.assertEqual([pos[c[k]] for k in ("pre", "c0", "anchor", "e1")],
                         ["before_lookback", "calibration_lookback", "anchor", "after_anchor"])

        def row(k, area, metric="comment_lines"):
            return [r for r in out["rows"] if (r["commit"], r["area"], r["metric"]) == (c[k], area, metric)][0]

        def fail(k, area, metric="comment_lines"):
            hits = [f for f in out["failure_index"] if f["rule"] == "v2" and
                    (f["commit"], f["area"], f["metric"]) == (c[k], area, metric)]
            return hits[0] if hits else None
        # e1: 10 <= 40/5 + 2 = 10 (boundary, proportional growth passes)
        r = row("e1", "Solidity/Core")
        self.assertEqual((r["numerator"], r["denominator"], r["allowance"], r["status"]), (10, 40, "10", "pass"))
        # e2: 11 > 10, prose rose without code; the cell already failed at pre (5 > 5/5 + 2)
        # and passed at c0 (4 <= 10/5 + 2), so it is reintroduced, not introduced
        f = fail("e2", "Solidity/Core")
        self.assertEqual((f["numerator"], f["allowance"], f["classification"]), (11, "10", "reintroduced"))
        self.assertEqual(fail("pre", "Solidity/Core")["classification"], "introduced")
        self.assertIn("prose_rose_without_code", f["causes"])
        # e3: code 40 -> 30, allowance 8, still 11 -> inherited, denominator shrank
        f = fail("e3", "Solidity/Core")
        self.assertEqual((f["allowance"], f["classification"], f["prior_status"]), ("8", "inherited", "fail"))
        self.assertIn("denominator_shrank", f["causes"])
        self.assertIsNone(fail("e4", "Solidity/Core"))                # 8 <= 8
        self.assertEqual(fail("e5", "Solidity/Core")["classification"], "reintroduced")
        # new area after calibration: frozen fallback, cannot train its own allowance
        f = fail("e2", "Solidity/New")
        self.assertEqual((f["case"], f["allowance"], f["denominator"]), ("unmapped_fallback", "0", 1))
        self.assertIn("unmapped_area", f["causes"])
        self.assertEqual([s["areas_outside_policy"] for s in out["commits"] if s["commit"] == c["e2"]],
                         [["Solidity/New"]])
        # blank docs lines are prose lines; d = 40 + 4 + 1 (New) = 45 Solidity code lines:
        # 5 > 45/12 + 7/6 = 59/12 (floor 4); docs/guide is measured, not enforced
        f = fail("e2", "docs/guide", "docs_lines")
        self.assertEqual((f["numerator"], f["denominator"], f["allowance"], f["allowance_floor"]),
                         (5, 45, "59/12", 4))
        self.assertFalse(f["enforced_in_proposal"])
        # zero code at evaluation: Z allowance = 0 * 0 + 2
        f = fail("e3", "Solidity/Z")
        self.assertEqual((f["numerator"], f["denominator"], f["allowance"]), (3, 0, "2"))
        self.assertIn("zero_code", f["causes"])
        self.assertIn("calibration_zero_code", f["causes"])
        self.assertIsNone(fail("e4", "Solidity/Z"))
        # process IDs and docstrings on the new Goals area
        f = fail("e5", "Solidity/Goals", "process_ids")
        self.assertEqual((f["numerator"], f["denominator"], f["allowance"]), (2, 4, "1"))
        self.assertEqual((f["classification"], f["prior_status"]), ("introduced", "pass"))
        self.assertIsNone(fail("e5", "Solidity/Goals", "docstring_lines"))
        self.assertEqual(row("e5", "Solidity/Goals", "docstring_lines")["allowance"], "2")
        # the pre-anchor commit is evaluated with later coefficients: 5 > 5/5 + 2
        self.assertEqual(fail("pre", "Solidity/Core")["position"], "before_lookback")
        # absent policy area: Goals before the anchor counts zero and passes
        self.assertEqual((row("c0", "Solidity/Goals")["present"], row("c0", "Solidity/Goals")["status"]),
                         (False, "pass"))
        # exhaustive index
        self.assertEqual(sum(1 for r in out["rows"] if r["in_window"] and r["status"] == "fail"),
                         len([f for f in out["failure_index"] if f["rule"] == "v2"]))
        enforced = out["totals"]["all"]["v2_enforced"]["failing_cells"]
        self.assertEqual(out["totals"]["all"]["v2"]["failing_cells"] - enforced,
                         sum(1 for f in out["failure_index"] if f["area"] == "docs/guide"))

    def test_code_padding_does_not_grow_denominator(self):
        c = self.build()
        policy = self.v2_calibrate(c["e1"])
        padded = lean(30, 9).replace("def x0 := 0", "\n\n-- pad\n/- pad\n-/\ndef x0 := 0")
        p = self.h.commit(T0 + 8 * DAY, {"Solidity/Core/A.lean": padded})
        out = self.v2_replay(p, policy, name="pad.json")
        r = [r for r in out["rows"] if (r["commit"], r["area"], r["metric"]) == (p, "Solidity/Core", "comment_lines")][0]
        # 2 blank lines add nothing; 3 comment lines add 3 prose lines, no code
        self.assertEqual((r["numerator"], r["denominator"], r["status"]), (12, 30, "fail"))

    def test_policy_immutable_deterministic_and_tamper_evident(self):
        c = self.build()
        policy = self.v2_calibrate(c["e1"])
        first = policy.read_bytes()
        self.h.commit(T0 + 8 * DAY, {"Solidity/Core/A.lean": lean(1, 50)})   # later history
        self.assertEqual(self.v2_calibrate(c["e1"]).read_bytes(), first)    # same frozen inputs
        self.v2_replay(c["e5"], policy, name="a.json")
        self.v2_replay(c["e5"], policy, name="b.json")
        self.assertEqual((self.out / "a.json").read_bytes(), (self.out / "b.json").read_bytes())
        self.assertEqual(policy.read_bytes(), first)
        data = json.loads(first)
        data["specification"]["selection"]["anchors"][0]["lookback"]["days"] = 3   # edit spec
        tampered = self.out / "tampered.json"
        tampered.write_text(json.dumps(data))
        with self.assertRaises(SystemExit):
            self.v2_replay(c["e5"], tampered, name="t.json")
        data = json.loads(first)
        data["calibration"]["Solidity/Core"]["metrics"]["comment_lines"]["margin"] = "3"  # hand raise
        tampered.write_text(json.dumps(data))
        with self.assertRaises(SystemExit):
            self.v2_replay(c["e5"], tampered, name="t.json")
        with self.assertRaises(SystemExit):                                   # pb1 file is not a policy
            self.v2_replay(c["e5"], self.calibrate(c["anchor"]), name="u.json")

    def test_verified_generated_versus_false_header(self):
        h = self.h
        gen = "/-! Generated by scripts/gen.py -/\n-- p\n-- q\ndef g := 1\n"   # 3 comment, 1 code
        c0 = h.commit(T0, {"scripts/gen.py": "print()\n", "Solidity/Core/A.lean": lean(10, 2),
                           "Solidity/Core/Gen.lean": gen, "docs/a.md": "a\n"})
        tree = dict(line.split("\t")[::-1] for line in h.git("ls-tree", "-r", c0).split("\n"))
        blob, gblob = tree["Solidity/Core/Gen.lean"].split()[2], tree["scripts/gen.py"].split()[2]
        c1 = h.commit(T0 + DAY, {"Solidity/Core/Gen.lean": gen + "-- r\n"})          # new blob
        c2 = h.commit(T0 + 2 * DAY, {"Solidity/Core/Gen.lean": gen, "scripts/gen.py": "print(1)\n"})
        verified = [{"path": "Solidity/Core/Gen.lean", "blob": blob, "generator_path": "scripts/gen.py",
                     "generator_blob": gblob, "scope": "file", "evidence": "synthetic"}]
        out = self.v2_replay(c2, self.v2_calibrate(c0, verified=verified, name="v.json"), name="g.json")
        got = {r["commit"]: (r["numerator"], r["denominator"]) for r in out["rows"]
               if (r["area"], r["metric"]) == ("Solidity/Core", "comment_lines")}
        self.assertEqual(got[c0], (2, 10))         # verified blob and generator: excluded both sides
        self.assertEqual(got[c1], (2 + 4, 11))     # edited output: counted as handwritten
        self.assertEqual(got[c2], (2 + 3, 11))     # generator changed: verification lapses
        # the same header without a verification record is padding and stays counted
        out = self.v2_replay(c2, self.v2_calibrate(c0, name="nv.json"), name="ng.json")
        got = {r["commit"]: (r["numerator"], r["denominator"]) for r in out["rows"]
               if (r["area"], r["metric"]) == ("Solidity/Core", "comment_lines")}
        self.assertEqual(got[c0], (5, 11))
        self.assertEqual(out["commits"][0]["generation_claims_counted_as_handwritten"], 1)

    def test_verified_block_and_old_mode_fields_unchanged(self):
        src = ("def a := 1\n-- BEGIN generated by scripts/gen.py\n-- G1 x\ndef b := 2\n"
               "-- END generated by scripts/gen.py\n-- H2\n")
        c = self.h.commit(T0, {"scripts/gen.py": "print()\n", "Solidity/Core/B.lean": src, "docs/a.md": "a\n"})
        repo = bt.Repo(self.h.root)
        blob = repo.blob_id(c, "Solidity/Core/B.lean")
        verified = [{"path": "Solidity/Core/B.lean", "blob": blob, "generator_path": "scripts/gen.py",
                     "generator_blob": repo.blob_id(c, "scripts/gen.py"), "scope": [2, 5], "evidence": "t"}]
        plain = bt.measure_commit(repo, bt.Analyzer(repo), c, None)
        m = bt.measure_commit(repo, bt.Analyzer(repo), c, None, verified)
        for key in plain:                           # old-mode fields are identical with v2 enabled
            if not key.startswith("v2"):
                self.assertEqual(plain[key], m[key], key)
        # outside lines 2-5: comment line 6 only; code line 1 only; H2 counted, G1 dropped
        self.assertEqual(m["v2"]["Solidity/Core"], {"docs_lines": 0, "comment_lines": 1,
                                                    "docstring_lines": 0, "process_ids": 1})
        self.assertEqual(m["v2_code"]["Solidity/Core"], 1)
        bad = self.h.commit(T0 + 1, {"Solidity/Bad/X.lean": b"\xff\xfe -- not utf-8\n"})
        mb = bt.measure_commit(repo, bt.Analyzer(repo), bad, None, verified)
        self.assertEqual((mb["v2"]["Solidity/Bad"], mb["v2_code"]["Solidity/Bad"]),
                         (dict.fromkeys(bt.METRICS, 0), 0))      # undecodable: area kept, reported
        self.assertIn("Solidity/Bad/X.lean", [u["path"] for u in mb["unknown"]])
        unverified = bt.measure_commit(repo, bt.Analyzer(repo), c, None, [])
        self.assertEqual(unverified["v2"]["Solidity/Core"]["comment_lines"], 4)
        self.assertEqual(unverified["v2_code"]["Solidity/Core"], 2)
        repo.close()

    def test_historical_rules_side_by_side(self):
        h = self.h
        bl = {"Solidity/Core": dict(docs_lines=0, comment_lines=2, docstring_lines=0, process_ids=0),
              "docs/guide": dict(docs_lines=2, comment_lines=0, docstring_lines=0, process_ids=0)}
        a = h.commit(T0, base_files(bl))
        b = h.commit(T0 + DAY, {"Solidity/Core/A.lean": lean(10, 3)})      # legacy fails, introduced
        h.commit(T0 + 2 * DAY, {"Solidity/Core/A.lean": lean(10, 2)})      # passes again
        d = h.commit(T0 + 3 * DAY, {"Solidity/Core/A.lean": lean(10, 3)})  # reintroduced
        pb1 = self.out / "pb1.json"
        with contextlib.redirect_stdout(io.StringIO()):
            bt.main(["--repo", str(h.root), "--end", d, "--days", "30",
                     "--estimate", str(self.calibrate(a)), "--output", str(pb1)])
        out = self.v2_replay(d, self.v2_calibrate(a, days=0), pb1=pb1)
        legacy = [(f["commit"], f["classification"]) for f in out["failure_index"]
                  if f["rule"] == "legacy" and f["area"] == "Solidity/Core" and f["metric"] == "comment_lines"]
        self.assertEqual(legacy, [(b, "introduced"), (d, "reintroduced")])
        old = json.loads(pb1.read_text())
        self.assertEqual(len([f for f in out["failure_index"] if f["rule"] in ("legacy", "pb1_ratio")]),
                         len([f for f in old["failure_index"] if f["rule"] in ("legacy", "ratio")]))
        self.assertEqual(old["schema"], "pb1-prose-backtest/1")
        self.assertEqual(out["historical_rules"]["legacy_states"], {"evaluated": 4})


if __name__ == "__main__":
    unittest.main()
