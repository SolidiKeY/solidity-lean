"""Accounting controls, never mocked successful semantic proofs."""
import copy
import unittest
import selection_ledger as ledger
from candidate_inventory import digest


class SelectionLedgerControls(unittest.TestCase):
    def inputs(self):
        source = "α old clause\nβ untouched\n"
        catalog = {"declarations": [
            {"id": "R.one", "kind": "constructor", "file": "Rules.lean", "span": {"start": 0, "stop": 13}, "clauses": [{"start": 6, "stop": 12}]},
            {"id": "R.two", "kind": "helper", "file": "Rules.lean", "span": {"start": 13, "stop": len(source)}, "clauses": [{"start": 13, "stop": len(source)}]}],
            "fixtures": [{"file": "oracle.lean", "sha256": "fixture identity"}], "frozen_manifests": [{"file": "profile.json"}]}
        manifest = {"cases": [{"id": "one", "constructor_id": "R.one", "kind": "mutant", "target": "Rules.lean", "old": "old", "new": "new", "target_sha256": digest(source.encode()), "mutant_sha256": digest(source.replace("old", "new").encode()), "oracle": "oracle.lean"}]}
        return catalog, manifest, {"Rules.lean": source}

    def test_every_candidate_and_unit_remains_visible(self):
        c, m, s = self.inputs(); result = ledger.account(c, m, s)
        self.assertEqual(result["counts"], {"declarations": 2, "units": 2, "fixtures": 1, "profiles": 1, "selected_ids": 1})
        self.assertEqual(result["declarations"][1]["disposition"], "unselected-candidate")
        self.assertEqual(result["declarations"][0]["units"][0]["touching_case_ids"], [])
        self.assertTrue(result["cases"][0]["outside_textual_units"])
        self.assertEqual(result["fixtures"][0]["selected_roles"], [{"case_id": "one", "role": "oracle"}])
        self.assertFalse(result["scope_complete"]); self.assertIsNone(result["score"])

    def test_unicode_offsets_and_zero_width_insertions(self):
        self.assertEqual(ledger.changed_spans("αb", "αxb", 7), [{"start": 8, "stop": 8, "kind": "insert"}])
        self.assertTrue(ledger.overlaps({"start": 8, "stop": 8}, {"start": 8, "stop": 9}))
        self.assertFalse(ledger.overlaps({"start": 9, "stop": 9}, {"start": 8, "stop": 9}))

    def test_omissions_duplicates_and_identity_tampering_fail(self):
        for fault in ("candidate", "fixture", "duplicate", "source", "mutant", "span"):
            c, m, s = self.inputs(); c = copy.deepcopy(c); m = copy.deepcopy(m)
            if fault == "candidate": c["declarations"].pop(0)
            if fault == "fixture": c["fixtures"] = []
            if fault == "duplicate": c["declarations"].append(copy.deepcopy(c["declarations"][0]))
            if fault == "source": m["cases"][0]["target_sha256"] = "0" * 64
            if fault == "mutant": m["cases"][0]["mutant_sha256"] = "0" * 64
            if fault == "span": c["declarations"][0]["span"]["start"] = 6
            with self.subTest(fault=fault), self.assertRaises(ValueError): ledger.account(c, m, s)
