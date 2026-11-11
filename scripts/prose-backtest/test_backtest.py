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


if __name__ == "__main__":
    unittest.main()
