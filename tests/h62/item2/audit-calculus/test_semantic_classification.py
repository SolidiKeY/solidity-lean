"""Regression controls: omitted signatures or duplicate roles cannot inflate review coverage."""
import contextlib
import io
import json
from unittest import mock
import copy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[4] / "scripts/h62/item2/audit-calculus"))
import classify_frozen_signatures as runner
from classify_frozen_signatures import authenticated_census, classify


class SemanticClassificationControls(unittest.TestCase):
    def setUp(self):
        row = {"id": "f:1:N.a", "file": "f", "line": 1, "source_name": "N.a", "signature_sha256": "exact"}
        self.source = {"base": "base", "declarations": [row, dict(row, id="g:2:N.b", file="g", line=2, source_name="N.b")]}
        self.curated = {"reviewed_file": "f", "declarations": [dict(row, name="N.a", global_proof_obligations={"proved": "universal"}, per_input_proof_facts={"run": "success premise"})]}

    def test_unreviewed_candidates_remain_in_denominator(self):
        result = classify(self.source, self.curated)
        self.assertEqual(result["counts"], {"source_candidates": 2, "role_reviewed": 1, "role_pending": 1, "semantic_owners_unresolved": 2, "new_joint_witnesses": 0})
        self.assertEqual(len(result["declarations"]), 2)

    def test_truncated_census_refused_before_classification(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "census.json"
            path.write_text("{}")
            with self.assertRaisesRegex(ValueError, "incomplete"):
                authenticated_census(path)

    def test_stale_signature_refused(self):
        self.curated["declarations"][0]["signature_sha256"] = "changed"
        with self.assertRaisesRegex(ValueError, "signature"):
            classify(self.source, self.curated)

    def test_duplicate_source_identity_refused(self):
        self.source["declarations"].append(copy.deepcopy(self.source["declarations"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate source"):
            classify(self.source, self.curated)

    def test_duplicate_review_refused(self):
        self.curated["declarations"] *= 2
        with self.assertRaisesRegex(ValueError, "duplicate"):
            classify(self.source, self.curated)

    def test_omitted_reviewed_file_declaration_refused(self):
        self.curated["declarations"] = []
        with self.assertRaisesRegex(ValueError, "unaccounted"):
            classify(self.source, self.curated)

    def test_multifile_review_requires_every_declared_file_candidate(self):
        self.curated.pop("reviewed_file")
        self.curated["reviewed_files"] = ["f", "g"]
        with self.assertRaisesRegex(ValueError, "unaccounted"):
            classify(self.source, self.curated)
        second = self.source["declarations"][1]
        self.curated["declarations"].append(dict(second, name=second["source_name"], global_proof_obligations={}, per_input_proof_facts={}))
        result = classify(self.source, self.curated)
        self.assertEqual(result["counts"]["role_reviewed"], 2)
        self.assertEqual(result["counts"]["semantic_owners_unresolved"], 2)
        self.assertEqual(result["counts"]["new_joint_witnesses"], 0)

    def test_unknown_or_repeated_reviewed_file_refused(self):
        for files in [["f", "missing"], ["f", "f"], [], [None]]:
            with self.subTest(files=files):
                self.curated["reviewed_files"] = files
                with self.assertRaisesRegex(ValueError, "reviewed file"):
                    classify(self.source, self.curated)


    def run_cli(self, arguments):
        # Synthetic Python runner controls, never formal proof/witness evidence.
        curated = dict(self.curated, base=self.source["base"],
                       source_census_sha256=runner.EXPECTED_CENSUS)
        output = io.StringIO()
        with mock.patch.object(sys, "argv", ["classify"] + arguments), \
             mock.patch.object(runner, "authenticated_census", return_value=self.source), \
             mock.patch.object(runner, "bulk_bytes", return_value=json.dumps(curated).encode()), \
             contextlib.redirect_stdout(output), contextlib.redirect_stderr(io.StringIO()):
            try:
                runner.main()
            except SystemExit as error:
                return error.code, output.getvalue()
        return 0, output.getvalue()

    def test_check_only_matches_report_counts_and_incomplete_exit_without_writes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            report = root / "report"
            common = ["--census", str(root / "fixture"), "--require-complete"]
            report_exit, report_stdout = self.run_cli(common + ["--out", str(report)])
            saved = json.loads((report / "classification.json").read_text())
            before = sorted(str(path.relative_to(root)) for path in root.rglob("*"))
            check_exit, check_stdout = self.run_cli(common + ["--check-only"])
            self.assertEqual((report_exit, check_exit), (1, 1))
            self.assertEqual(json.loads(report_stdout), saved["counts"])
            self.assertEqual(check_stdout, report_stdout)
            self.assertEqual(before, sorted(str(path.relative_to(root)) for path in root.rglob("*")))
            self.assertEqual(saved["counts"]["new_joint_witnesses"], 0)

    def test_check_only_retains_signature_validation(self):
        self.curated["declarations"][0]["signature_sha256"] = "stale"
        with self.assertRaisesRegex(ValueError, "signature"):
            self.run_cli(["--census", "fixture", "--check-only"])

    def test_output_modes_are_required_and_mutually_exclusive(self):
        for modes in [[], ["--check-only", "--out", "unused"]]:
            with self.subTest(modes=modes):
                code, output = self.run_cli(["--census", "fixture"] + modes)
                self.assertEqual(code, 2)
                self.assertEqual(output, "")

    def test_report_mode_keeps_repository_output_refusal(self):
        code, output = self.run_cli(["--census", "fixture", "--out", str(runner.REPO)])
        self.assertEqual(code, 2)
        self.assertEqual(output, "")

    def owner_record(self):
        self.source["sources"] = [{"path": "f", "sha256": "0" * 64}, {"path": "g", "sha256": "1" * 64}]
        return {"status": "confirmed", "owner": "master (coordinator), no live producer",
                "authority_kind": "coordinator-user-answer", "authority": "Q-SEM-OWNER-01, GitHub #52",
                "source_sha256": "0" * 64}

    def test_explicit_owner_confirmation_is_separate_from_role_review(self):
        self.curated["semantic_owner_by_file"] = {"f": self.owner_record()}
        result = classify(self.source, self.curated)
        self.assertEqual(result["counts"]["semantic_owners_unresolved"], 1)
        self.assertEqual(result["counts"]["role_pending"], 1)
        self.assertEqual(result["counts"]["new_joint_witnesses"], 0)

    def test_owner_confirmation_can_cover_an_unreviewed_role(self):
        owner = self.owner_record()
        owner["source_sha256"] = "1" * 64
        self.curated["semantic_owner_by_file"] = {"g": owner}
        result = classify(self.source, self.curated)
        self.assertEqual(result["counts"]["semantic_owners_unresolved"], 1)
        self.assertEqual(result["declarations"][1]["semantic_owner"]["status"], "confirmed")
        self.assertIn("pending", result["declarations"][1]["role_status"])

    def test_family_hint_is_not_authoritative_confirmation(self):
        owner = self.owner_record()
        owner["authority_kind"] = "migration-writer-hint"
        self.curated["semantic_owner_by_file"] = {"f": owner}
        with self.assertRaisesRegex(ValueError, "authoritative"):
            classify(self.source, self.curated)

    def test_changed_or_unknown_owner_source_refused(self):
        owner = self.owner_record()
        owner["source_sha256"] = "changed"
        self.curated["semantic_owner_by_file"] = {"f": owner}
        with self.assertRaisesRegex(ValueError, "source hash"):
            classify(self.source, self.curated)
        self.curated["semantic_owner_by_file"] = {"unknown": owner}
        with self.assertRaisesRegex(ValueError, "unknown semantic-owner"):
            classify(self.source, self.curated)

    def test_role_annotation_alone_cannot_confirm_owner(self):
        self.curated["declarations"][0]["semantic_owner"] = {"status": "confirmed", "owner": "unsupported guess"}
        self.assertEqual(classify(self.source, self.curated)["counts"]["semantic_owners_unresolved"], 2)

    def test_premise_cannot_be_both_global_and_local(self):
        self.curated["declarations"][0]["per_input_proof_facts"]["proved"] = "incorrect local role"
        with self.assertRaisesRegex(ValueError, "two roles"):
            classify(self.source, self.curated)


if __name__ == "__main__":
    unittest.main()
