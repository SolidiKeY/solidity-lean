"""Guard loss of source premises and silent candidate omission on parse failure."""
import copy
import unittest
from unittest.mock import patch
from census import sha
import source_roles


class SourceRoleAccounting(unittest.TestCase):
    def census(self, text):
        row = {"id": "fixture:1:t", "path": "fixture", "line": 1,
               "source_signature": text, "signature_sha256": sha(text.encode()),
               "section_variables": ["variable (h : False)"]}
        return {"base": "fixture", "sources": {"fixture": {"sha256": sha(text.encode())}},
                "declarations": [row], "summary": {"files": 1, "source_candidates": 1}}

    def run_fixture(self, failure=False, duplicate=False, corrupt=False):
        text = "theorem t (h : False) : True := by trivial"
        census = self.census(text)
        if duplicate:
            census["declarations"] *= 2
        if corrupt:
            census["sources"]["fixture"]["sha256"] = "0" * 64
        result = {"source_id": "fixture:1:t", "in_scope": True, "exclusion": None}
        with patch.object(source_roles, "source_census", return_value=census), \
             patch.object(source_roles, "frozen_sources", return_value={"fixture": text}), \
             patch.object(source_roles, "declaration_index", return_value=({}, {})), \
             patch.object(source_roles, "classify_row", side_effect=ValueError("fixture failure") if failure else None, return_value=result):
            return source_roles.generate()

    def test_error_keeps_premises_and_scope(self):
        report = self.run_fixture(failure=True)
        row = report["declarations"][0]
        self.assertEqual(report["summary"]["source_parse_errors"], 1)
        self.assertIn("(h : False)", row["source_signature"])
        self.assertEqual(row["section_variables"], ["variable (h : False)"])
        self.assertTrue(row["in_scope"])
        self.assertIsNone(row["exclusion"])
        self.assertIsNone(row["owner"])
        self.assertFalse(report["historical_replay"])
        self.assertFalse(report["kernel_checked"])
        self.assertEqual(report["certified_witnesses"], 0)

    def test_duplicate_fails(self):
        with self.assertRaisesRegex(ValueError, "accounting mismatch"):
            self.run_fixture(duplicate=True)

    def test_source_drift_fails(self):
        with self.assertRaisesRegex(ValueError, "frozen source mismatch"):
            self.run_fixture(corrupt=True)


class RefinementBoundary(unittest.TestCase):
    def report(self):
        return {"parse_errors": [], "summary": {}, "declarations": [{
            "source_id": "fixture:1:t", "source_signature": "theorem t (h : False) : True",
            "signature_sha256": "fixed", "section_variables": ["variable (h : False)"],
            "owner": None, "owner_status": "UNVERIFIABLE-historical-snapshot",
            "in_scope": True, "exclusion": None}]}

    def refine_with(self, changed):
        original = self.report()
        with patch.object(source_roles, "frozen_sources", return_value={}), \
             patch.object(source_roles, "declaration_index", return_value=({}, {})), \
             patch("refine_remaining.fact", return_value={}), \
             patch("refine_remaining.refine", return_value=(changed, [])):
            return source_roles.refine_known_domains(original)

    def test_changed_premise_refused(self):
        changed = copy.deepcopy(self.report())
        changed["declarations"][0]["source_signature"] = "theorem t : True"
        with self.assertRaisesRegex(ValueError, "claim boundary"):
            self.refine_with(changed)

    def test_omitted_candidate_refused(self):
        changed = self.report()
        changed["declarations"] = []
        with self.assertRaisesRegex(ValueError, "candidate count"):
            self.refine_with(changed)

    def test_unknown_owner_cannot_be_filled(self):
        changed = self.report()
        changed["declarations"][0]["owner"] = "invented-owner"
        with self.assertRaisesRegex(ValueError, "claim boundary"):
            self.refine_with(changed)


if __name__ == "__main__":
    unittest.main()
