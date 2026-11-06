"""Source-accounting controls; never mocked successful semantic proofs."""
import copy
import unittest
import selection_ledger as ledger
import candidate_inventory as census


class SelectionLedgerControls(unittest.TestCase):
    SOURCE = "-- α\nnamespace Solidity\ninductive Taclet where\n  | one : dl{ [ ] ⇝ true }\n  | two : dl{ [ ] ⇝ false }\nend Solidity\n"

    def inputs(self, source=None):
        source = self.SOURCE if source is None else source
        rules, callbacks = census.INPUTS[:2]
        sources = {rules: source, callbacks: "namespace Solidity\nend Solidity\n"}
        inputs = {f: census.digest(s.encode()) for f, s in sources.items()}
        rows = []
        for file, text in sources.items():
            for row in census.declarations(text, file):
                row["clauses"] = census.premise_clauses(text, row); rows.append(row)
        catalog = {"production_inputs": inputs, "declarations": rows,
                   "fixtures": [{"file": "oracle.lean", "sha256": "accounting fixture"}],
                   "frozen_manifests": [{"file": "profile.json"}]}
        case = {"id": "one", "constructor_id": "Taclet.one", "kind": "mutant", "target": rules,
                "old": "one", "new": "renamed", "target_sha256": census.digest(source.encode()),
                "mutant_sha256": census.digest(source.replace("one", "renamed").encode()), "oracle": "oracle.lean"}
        manifest = {"base": census.BASE, "production_inputs": inputs, "cases": [case]}
        span = rows[0]["span"]
        inventory = {"base": census.BASE, "production_inputs": inputs, "inventory": [
            {"id": "Taclet.one", "file": rules, "line_start": span["line_start"], "line_end": span["line_end"], "span_sha256": span["sha256"]}]}
        manifest["declared_case_counts"] = ledger.case_counts(manifest["cases"])
        return catalog, manifest, sources, inventory

    def test_every_candidate_and_unit_remains_visible(self):
        result = ledger.account(*self.inputs())
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

    def test_dropping_an_unselected_candidate_is_rejected(self):
        c, m, s, i = self.inputs(); c["declarations"].pop(1)
        with self.assertRaisesRegex(ValueError, "exhaustive source declarations"):
            ledger.account(c, m, s, i)

    def test_edit_text_must_occur_exactly_once(self):
        c, m, s, i = self.inputs(self.SOURCE + "-- one\n")
        with self.assertRaisesRegex(ValueError, "source attribution mismatch"):
            ledger.account(c, m, s, i)
        c, m, s, i = self.inputs(); m["cases"][0]["old"] = "missing edit text"
        with self.assertRaisesRegex(ValueError, "source attribution mismatch"):
            ledger.account(c, m, s, i)

    def test_duplicate_scored_program_is_rejected(self):
        c, m, s, i = self.inputs(); second = copy.deepcopy(m["cases"][0]); second.update(id="other", kind="negative-control"); m["cases"].append(second)
        with self.assertRaisesRegex(ValueError, "duplicate mutant hash"):
            ledger.account(c, m, s, i)

    def test_only_linked_survivor_duplicate_is_allowed(self):
        c, m, s, i = self.inputs(); control = copy.deepcopy(m["cases"][0]); control.update(id="control.one", kind="runner-survivor-control", control_of="one", regression="oracle.lean"); m["cases"].append(control)
        m["declared_case_counts"] = ledger.case_counts(m["cases"])
        self.assertEqual(ledger.account(c, m, s, i)["counts"]["selected_ids"], 2)
        for fault in ("wrong-parent", "independent-known-kill", "no-regression", "unique-unlinked-survivor"):
            altered = copy.deepcopy(m)
            if fault == "wrong-parent": altered["cases"][1]["control_of"] = "absent"
            if fault == "independent-known-kill": altered["cases"][1]["kind"] = "known-kill"
            if fault == "no-regression": altered["cases"][1].pop("regression")
            if fault == "unique-unlinked-survivor": altered["cases"][1]["mutant_sha256"] = "0" * 64
            with self.subTest(fault=fault), self.assertRaisesRegex(ValueError, "duplicate mutant hash"):
                ledger.account(c, altered, s, i)

        altered = copy.deepcopy(m)
        parent = copy.deepcopy(m["cases"][0]); parent.update(id="second", mutant_sha256="f" * 64)
        survivor = copy.deepcopy(m["cases"][1]); survivor.update(id="control.second", control_of="second", mutant_sha256="f" * 64)
        altered["cases"].extend([parent, survivor])
        with self.assertRaisesRegex(ValueError, "multiple survivor controls"):
            ledger.account(c, altered, s, i)

    def test_omissions_and_span_identity_tampering_fail(self):
        for fault in ("selected-candidate", "fixture", "duplicate", "source", "mutant", "catalog-span", "index-span", "index-input"):
            c, m, s, i = self.inputs()
            if fault == "selected-candidate": c["declarations"].pop(0)
            if fault == "fixture": c["fixtures"] = []
            if fault == "duplicate": c["declarations"].append(copy.deepcopy(c["declarations"][0]))
            if fault == "source": m["cases"][0]["target_sha256"] = "0" * 64
            if fault == "mutant": m["cases"][0]["mutant_sha256"] = "0" * 64
            if fault == "catalog-span": c["declarations"][0]["span"]["start"] += 1
            if fault == "index-span": i["inventory"][0]["span_sha256"] = "0" * 64
            if fault == "index-input": i["production_inputs"] = {}
            with self.subTest(fault=fault), self.assertRaises(ValueError): ledger.account(c, m, s, i)

    def test_declared_counts_cannot_conflate_control_duplicates(self):
        c, m, s, i = self.inputs(); control = copy.deepcopy(m["cases"][0]); control.update(id="control.one", kind="runner-survivor-control", control_of="one", regression="oracle.lean"); m["cases"].append(control)
        m["declared_case_counts"] = ledger.case_counts(m["cases"])
        result = ledger.account(c, m, s, i)
        self.assertEqual(result["program_counts"]["distinct_scored_programs"], 1)
        self.assertEqual(result["program_counts"]["distinct_programs_all_roles"], 1)
        self.assertEqual(result["program_counts"]["case_ids"], 2)
        m["declared_case_counts"]["distinct_scored_programs"] = 0
        with self.assertRaisesRegex(ValueError, "declared case/program counts mismatch"):
            ledger.account(c, m, s, i)

    def test_omitted_declared_counts_are_rejected(self):
        c, m, s, i = self.inputs(); m.pop("declared_case_counts")
        with self.assertRaisesRegex(ValueError, "declared case counts are required"):
            ledger.account(c, m, s, i)
