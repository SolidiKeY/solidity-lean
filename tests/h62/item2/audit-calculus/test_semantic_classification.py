"""Regression controls: omitted signatures or duplicate roles cannot inflate review coverage."""
import copy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[4] / "scripts/h62/item2/audit-calculus"))
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

    def test_premise_cannot_be_both_global_and_local(self):
        self.curated["declarations"][0]["per_input_proof_facts"]["proved"] = "incorrect local role"
        with self.assertRaisesRegex(ValueError, "two roles"):
            classify(self.source, self.curated)


if __name__ == "__main__":
    unittest.main()
