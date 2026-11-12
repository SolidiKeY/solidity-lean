import copy
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "check-prose-budget"
M = runpy.run_path(str(SCRIPT))
KEY = M["CANDIDATE_KEY"]
POLICY = json.loads((SCRIPT.parent / "prose-baseline.json").read_text())[KEY]


class Arithmetic(unittest.TestCase):
    def test_independent_boundaries(self):
        for entry in ({"ratio": "1/2", "margin": "1/2"},
                      {"ratio": "2/4", "margin": "3/6"}):
            for n, d, expected, floor in ((1, 1, True, 1), (2, 1, False, 1),
                                          (0, 0, True, 0), (1, 0, False, 0),
                                          (5, 9, True, 5), (6, 9, False, 5)):
                self.assertEqual(M["allowance"](n, d, entry), (expected, floor))
        self.assertEqual(M["allowance"](1, 0, {"ratio": "0", "margin": "3/2"}), (True, 1))
        for entry in (None, {"ratio": "0", "margin": "0"}):
            self.assertEqual(M["allowance"](0, 1000, entry), (True, 0))
            self.assertEqual(M["allowance"](1, 1000, entry), (False, 0))

    def test_invalid(self):
        for value in (True, 0.5, 1, None, "-1", "1/0", "nan", "1.5", "1/-2"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                M["rational"](value)
        for n, d in ((-1, 1), (1, -1), (True, 1), (1, None)):
            with self.assertRaises(ValueError):
                M["allowance"](n, d)

    def test_padding_lexer(self):
        cases = [
            ("\n \t\u2003\n-- c\n/- a\n/- b -/\n-/\n", 0),
            ("def x := 1 /- c -/\n", 1),
            ("def x := r##\"/- literal\n \u2003\n-/\"##\n", 2),
            ("def «/- quoted -/» := 1\n", 1),
            ("def x := s!\"{ /- comment\n-only -/ 1 }\"\n", 2),
        ]
        for source, expected in cases:
            with self.subTest(source=source):
                self.assertEqual(M["code_measurement"](source)[1], expected)


class CandidateCLI(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "Solidity/Automation").mkdir(parents=True)
        (self.root / "docs/guide").mkdir(parents=True)
        self.lean = self.root / "Solidity/Automation/A.lean"
        self.lean.write_text("def x := 1\n")
        self.baseline = self.root / "baseline.json"
        self.policy = copy.deepcopy(POLICY)
        self.proposal = self.root / "proposal.json"
        self.save()

    def save(self):
        doc = M["counts"](self.root)
        doc[KEY] = self.policy
        self.baseline.write_text(json.dumps(doc))

    def run_cli(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), "--root", str(self.root),
                               "--baseline", str(self.baseline), *args], capture_output=True, text=True)

    def test_proportional_and_density_growth_and_isolation(self):
        # 28/38 is the frozen comment ratio, with zero margin.
        self.lean.write_text(("def x := 1 -- comment\n" * 28) + "def y := 2\n" * 10)
        self.save()
        self.assertEqual(self.run_cli("--calibrated-check").returncode, 0)
        self.lean.write_text(self.lean.read_text() * 2)
        candidate = self.run_cli("--calibrated-check")
        self.assertEqual(candidate.returncode, 0, candidate.stderr)
        legacy = self.run_cli()
        self.assertEqual(legacy.returncode, 1)
        self.assertIn("56 > 28", legacy.stderr)
        self.lean.write_text(self.lean.read_text() + "-- extra\n")
        self.assertEqual(self.run_cli("--calibrated-check").returncode, 1)
        self.lean.write_text(self.lean.read_text() + "\n \t\u2003\n" * 100)
        self.assertEqual(self.run_cli("--calibrated-check").returncode, 1)

    def test_reach_and_audits_exemption(self):
        (self.root / "docs/audits").mkdir()
        (self.root / "docs/audits/raw.bin").write_text("audit\n" * 500)
        (self.root / "docs/root.md").write_text("root\n")
        (self.root / "Solidity/root.lean").write_text("def y := 0\n")
        rows, code = M["calibrated_counts"](self.root)
        self.assertEqual(rows["docs/audits"]["docs_lines"], 500)
        self.assertEqual(rows["docs/_root"]["docs_lines"], 1)
        self.assertEqual(code["Solidity/_root"], 1)
        outcome = self.run_cli("--calibrated-check")
        self.assertEqual(outcome.returncode, 0, outcome.stderr)
        self.assertIn("docs/audits docs_lines: 500", outcome.stdout)
        self.assertIn("EXEMPT", outcome.stdout)
        (self.root / "docs/guide/a.md").write_text("unseen\n")
        self.assertEqual(self.run_cli("--calibrated-check").returncode, 1)

    def test_source_local_and_docs_global(self):
        # docs/module-map ratio is 808/74127: 92 eligible lines permit 1 doc line.
        (self.root / "docs/module-map").mkdir()
        (self.root / "docs/module-map/a.md").write_text("one\n")
        self.lean.write_text("def x := 0\n" * 91)
        self.assertEqual(self.run_cli("--calibrated-check").returncode, 1)
        (self.root / "Solidity/Other").mkdir()
        (self.root / "Solidity/Other/B.lean").write_text("def y := 0\n")
        outcome = self.run_cli("--calibrated-check")
        self.assertEqual(outcome.returncode, 0, outcome.stderr)
        self.assertIn("docs/module-map docs_lines: 1 <= 1 (denominator 92)", outcome.stdout)
        self.assertIn("Solidity/Automation comment_lines: 0 <= 67 (denominator 91)", outcome.stdout)

    def test_all_metrics_and_registry_occurrences(self):
        self.lean.write_text("/-- H13 G2 H14 -/\ndef x := \"H99\" -- GH1 XH2 H3x\n")
        rows, code = M["calibrated_counts"](self.root)
        self.assertEqual(rows["Solidity/Automation"], dict(docs_lines=0, comment_lines=2,
                                                         docstring_lines=1, process_ids=4))
        self.assertEqual(code["Solidity/Automation"], 1)
        (self.root / "Solidity.lean").write_text("import Solidity.Automation.G1\n")
        self.lean.write_text("import Solidity.Automation.G1\n-- G1 G1\n")
        self.assertEqual(M["calibrated_counts"](self.root)[0]["Solidity/Automation"]["process_ids"], 2)

    def test_each_metric_subprocess_boundary(self):
        self.lean.write_text("/-- H1 -/\n" + "def x := 0\n" * 1000)
        (self.root / "docs/module-map").mkdir()
        (self.root / "docs/module-map/a.md").write_text("one\n")
        for metric in M["METRICS"]:
            self.policy = copy.deepcopy(POLICY)
            area = "docs/module-map" if metric == "docs_lines" else "Solidity/Automation"
            # At zero allowance exactly zero passes, one fails independently.
            self.policy["areas"][area][metric] = dict(ratio="0", margin="0")
            self.save()
            result = self.run_cli("--calibrated-check")
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertIn(f"{area} {metric}: 1 <= 0", result.stdout)
            self.policy["areas"][area][metric] = dict(ratio="0", margin="1")
            self.save()
            self.assertEqual(self.run_cli("--calibrated-check").returncode, 0)

    def test_missing_policy_cells_zero_allowance(self):
        self.lean.write_text("-- comment\n")
        del self.policy["areas"]["Solidity/Automation"]["comment_lines"]
        self.save()
        result = self.run_cli("--calibrated-check")
        self.assertEqual(result.returncode, 1)
        self.assertIn("comment_lines: 1 <= 0", result.stdout)
        del self.policy["areas"]["Solidity/Automation"]
        self.save()
        self.assertEqual(self.run_cli("--calibrated-check").returncode, 1)

    def test_errors_fail_closed(self):
        for source in (b"\xff", b"/- unclosed", b"def x := \"unclosed"):
            self.lean.write_bytes(source)
            self.assertEqual(self.run_cli("--calibrated-check").returncode, 2)
        self.lean.write_text("def «unclosed := 0\n")
        self.assertEqual(self.run_cli("--calibrated-check").returncode, 2)
        self.lean.unlink()
        self.lean.parent.rmdir()
        (self.root / "Solidity").rmdir()
        self.assertEqual(self.run_cli("--calibrated-check").returncode, 2)
        self.lean.parent.mkdir(parents=True)
        self.lean.write_text("def x := 0\n")
        with patch.object(Path, "read_bytes", side_effect=PermissionError("unreadable")):
            with self.assertRaises(OSError):
                M["calibrated_counts"](self.root)

    def test_update_explicit_shrink_only_and_atomic(self):
        before = self.baseline.read_bytes()
        self.assertEqual(self.run_cli("--calibrated-check", "--update").returncode, 2)
        self.assertEqual(before, self.baseline.read_bytes())
        old = copy.deepcopy(self.policy)
        for ratio, margin in (("15/19", "0"), ("0", "1")):
            proposal = copy.deepcopy(old)
            proposal["areas"]["Solidity/Automation"]["comment_lines"] = dict(ratio=ratio, margin=margin)
            self.proposal.write_text(json.dumps(proposal))
            self.assertEqual(self.run_cli("--calibrated-check", "--update", "--candidate-proposal", str(self.proposal)).returncode, 2)
            self.assertEqual(before, self.baseline.read_bytes())
        for malformed in ("{", "null", "{}"):
            self.proposal.write_text(malformed)
            self.assertEqual(self.run_cli("--calibrated-check", "--update", "--candidate-proposal", str(self.proposal)).returncode, 2)
            self.assertEqual(before, self.baseline.read_bytes())
        self.proposal.write_text(json.dumps(old))
        self.assertEqual(self.run_cli("--calibrated-check", "--update", "--candidate-proposal", str(self.proposal)).returncode, 0)
        old["areas"]["Solidity/Automation"]["comment_lines"]["ratio"] = "1/2"
        self.proposal.write_text(json.dumps(old))
        self.assertEqual(self.run_cli("--calibrated-check", "--update", "--candidate-proposal", str(self.proposal)).returncode, 0)
        self.assertEqual(json.loads(self.baseline.read_text())[KEY], old)
        self.assertEqual(self.run_cli("--update").returncode, 0)
        self.assertEqual(json.loads(self.baseline.read_text())[KEY], old)

    def test_tradeoff_refusal_equivalent_fraction_and_missing_proposal(self):
        before = self.baseline.read_bytes()
        self.assertEqual(self.run_cli("--calibrated-check", "--update", "--candidate-proposal", str(self.proposal)).returncode, 2)
        for ratio, margin in (("1", "0"), ("0", "4000")):
            proposal = copy.deepcopy(self.policy)
            proposal["areas"]["Solidity/Backend"]["comment_lines"] = dict(ratio=ratio, margin=margin)
            self.proposal.write_text(json.dumps(proposal))
            result = self.run_cli("--calibrated-check", "--update", "--candidate-proposal", str(self.proposal))
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assertEqual(before, self.baseline.read_bytes())
        proposal = copy.deepcopy(self.policy)
        proposal["areas"]["Solidity/Automation"]["comment_lines"]["ratio"] = "28/38"
        self.proposal.write_text(json.dumps(proposal))
        self.assertEqual(self.run_cli("--calibrated-check", "--update", "--candidate-proposal", str(self.proposal)).returncode, 0)

    def test_frozen_published_coefficients(self):
        calibration = json.loads((SCRIPT.parent / "prose-backtest/calibration-additive.json").read_text())
        expected = {a: {k: dict(ratio=v["ratio"], margin=v["margin"]) for k, v in row["metrics"].items()}
                    for a, row in calibration["calibration"].items()}
        self.assertEqual(POLICY["areas"], expected)
        self.assertEqual(POLICY["denominator_mapping"], calibration["specification"]["denominator_mapping"])

    def test_generated_docs_and_padding_invariance(self):
        generator = self.root / "generator.py"
        generator.write_text("generator")
        doc = self.root / "docs/guide/generated.md"
        doc.write_text("generated\n" * 100)
        entry = dict(path="docs/guide/generated.md", blob=M["blob_id"](doc.read_bytes()),
                     generator_path="generator.py", generator_blob=M["blob_id"](generator.read_bytes()), scope="file")
        before_rows, before_code = M["calibrated_counts"](self.root, [entry])
        self.assertEqual(before_rows["docs/guide"]["docs_lines"], 0)
        doc.unlink()
        after_rows, after_code = M["calibrated_counts"](self.root, [entry])
        self.assertEqual(before_code.get("Solidity/Automation"), after_code.get("Solidity/Automation"))
        self.assertTrue(all(not any(row.values()) for a, row in before_rows.items() if a.startswith("docs/")))

    def test_legacy_fixture_decision_and_counts_golden(self):
        self.lean.write_text("/-- H1 -/\ndef x := 0 -- G2\n")
        (self.root / "docs/guide/a.md").write_text("one\ntwo\n")
        self.save()
        self.assertEqual(M["counts"](self.root), {
            "Solidity/Automation": dict(docs_lines=0, comment_lines=2, docstring_lines=1, process_ids=2),
            "docs/guide": dict(docs_lines=2, comment_lines=0, docstring_lines=0, process_ids=0)})
        self.assertEqual(self.run_cli().stdout, "Prose budget PASS (2 areas)\n")
        self.lean.write_text(self.lean.read_text() + "-- c\n")
        result = self.run_cli()
        self.assertEqual((result.returncode, result.stdout, result.stderr),
                         (1, "", "Prose budget exceeded:\nSolidity/Automation comment_lines: 3 > 2\n"))

    def test_frozen_metadata_and_scope(self):
        for mutate in (lambda p: p.update(active=True),
                       lambda p: p["enforcement_exclusions"].update({"docs/guide": "approve"}),
                       lambda p: p["areas"].pop("Solidity/Automation"),
                       lambda p: p["areas"]["Solidity/Automation"].pop("comment_lines"),
                       lambda p: p["verified_generated"].append({"path": "forged"})):
            proposal = copy.deepcopy(self.policy)
            mutate(proposal)
            self.proposal.write_text(json.dumps(proposal))
            before = self.baseline.read_bytes()
            result = self.run_cli("--calibrated-check", "--update", "--candidate-proposal", str(self.proposal))
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assertEqual(before, self.baseline.read_bytes())

    def test_generation_identity_and_false_headers(self):
        generator = self.root / "scripts/generate.py"
        generator.parent.mkdir()
        generator.write_text("generator identity\n")
        self.lean.write_text("-- Generated by scripts/generate.py\ndef x := 1 -- H1\n")
        data = self.lean.read_bytes()
        def git_blob(data):
            return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        entry = dict(path="Solidity/Automation/A.lean", blob=git_blob(data),
                     generator_path="scripts/generate.py", generator_blob=git_blob(generator.read_bytes()), scope="file")
        rows, code = M["calibrated_counts"](self.root, [entry])
        self.assertEqual(sum(rows["Solidity/Automation"].values()), 0)
        self.assertEqual(code["Solidity/Automation"], 0)
        rows, code = M["calibrated_counts"](self.root)
        self.assertEqual(rows["Solidity/Automation"]["comment_lines"], 2)
        self.assertEqual(code["Solidity/Automation"], 1)
        for field in ("path", "blob", "generator_blob", "generator_path"):
            changed = dict(entry)
            changed[field] = "other" if field != "generator_path" else "scripts/other.py"
            if field == "generator_path":
                (self.root / changed[field]).write_text("different generator")
            self.assertEqual(M["calibrated_counts"](self.root, [changed])[1]["Solidity/Automation"], 1)
        self.lean.write_bytes(data + b"-- padding\n")
        self.assertEqual(M["calibrated_counts"](self.root, [entry])[1]["Solidity/Automation"], 1)
        self.assertEqual(POLICY["verified_generated"], [])

    def test_workflow_and_default_metadata_isolation(self):
        workflow = (SCRIPT.parent.parent / ".github/workflows/prose-budget.yml").read_text()
        self.assertIn("- run: python3 scripts/check-prose-budget\n", workflow)
        self.assertIn("- run: python3 -m unittest discover -s scripts/check-prose-budget-tests", workflow)
        self.assertNotIn("continue-on-error", workflow)
        self.assertNotIn("--calibrated", workflow)
        # Candidate metadata is never a default success/failure input.
        self.policy["active"] = True
        self.save()
        self.assertEqual(self.run_cli().returncode, 0)
        self.assertEqual(self.run_cli("--calibrated-check").returncode, 2)


if __name__ == "__main__":
    unittest.main()
