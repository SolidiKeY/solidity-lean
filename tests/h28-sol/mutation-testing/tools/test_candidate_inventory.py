"""Census/parser controls only; actual Lean gates establish typed facts."""
from pathlib import Path
import collections
import unittest
from unittest.mock import patch
import subprocess
import tempfile
import check_candidate_inventory as audit
import candidate_inventory as census


class CandidateInventoryControls(unittest.TestCase):
    def test_comments_strings_and_primed_identifiers_preserve_offsets(self):
        source = "α /- outer /- | fake -/ nested -/ Γ' -- hidden\n\"label; \\\"x\" ';' '\\n'"
        clean = census.mask(source)
        self.assertEqual(len(clean), len(source))
        self.assertEqual([i for i, c in enumerate(clean) if c == "\n"], [i for i, c in enumerate(source) if c == "\n"])
        self.assertNotIn("fake", clean)
        self.assertIn("Γ'", clean)
        self.assertNotIn(";", clean)

    def test_unclosed_comments_and_strings_fail(self):
        for source in ["/- never ends", '"never ends']:
            with self.assertRaises(ValueError): census.mask(source)

    def test_dsl_clauses_ignore_statement_and_label_semicolons(self):
        source = 'namespace Solidity\ninductive Taclet where\n  | branches : dl{ [ f(); ] ⇝ "first; label": { x := f(1, 2) } []; "second": [ g(); ] }\nend Solidity\n'
        rows = census.declarations(source, "fixture")
        clauses = census.premise_clauses(source, rows[0])
        self.assertEqual(len(clauses), 2)
        self.assertTrue(all(c["kind"] == "dsl-premise-branch" for c in clauses))
        self.assertIn('"second"', source[clauses[1]["start"]:clauses[1]["stop"]])

    def test_no_missing_or_unbalanced_premise_is_accepted(self):
        for body in ['dl{ [] }', 'dl{ [] ⇝ [ }']:
            source = "namespace Solidity\ninductive Taclet where\n  | bad : " + body + "\nend Solidity\n"
            row = census.declarations(source, "fixture")[0]
            with self.assertRaises(ValueError): census.premise_clauses(source, row)

    def test_typed_constructor_and_enum_alternatives_are_retained(self):
        source = "namespace Solidity\ninductive Rule where\n  | key (d : Nat)\n  | lean (d : Bool)\nend Solidity\n"
        rows = census.declarations(source, "fixture")
        self.assertEqual([r["id"] for r in rows], ["Rule.key", "Rule.lean"])
        self.assertEqual(census.premise_clauses(source, rows[0])[0]["kind"], "typed-declaration-body")
        self.assertEqual(census.enum_names("inductive BinOp where\n  | add | sub | mul\n  deriving Repr\n", "BinOp"), ["add", "sub", "mul"])

    def test_unicode_byte_spans_are_not_character_offsets(self):
        row = census.span("α\nβ", 0, 1)
        self.assertEqual(row["byte_stop"], 2)
        self.assertEqual(row["line_start"], 1)

    def test_full_pinned_census_and_existing_fixture_inventories(self):
        root = Path(__file__).resolve().parents[4]
        data = census.build(root)
        owners = collections.Counter(r["id"].split(".")[0] for r in data["declarations"] if r["kind"] == "constructor")
        self.assertEqual(dict(owners), {"Taclet": 181, "LeanTaclet": 28, "Rule": 2, "CallbackTaclet": 4})
        kinds = collections.Counter(r["kind"] for r in data["declarations"])
        self.assertEqual(dict(kinds), {"constructor": 215, "existing-theorem": 3, "term-helper": 55, "side-condition-helper": 17})
        self.assertIn("Loc.isTarget", {r["id"] for r in data["declarations"]})
        self.assertIn("CallbackTaclet.toTaclet", {r["id"] for r in data["declarations"]})
        self.assertEqual(len(data["fixtures"]), 34)
        self.assertEqual(len(data["frozen_manifests"]), 13)
        self.assertEqual(len(data["case_variants"]), 19)
        self.assertEqual(len(data["binop_acceptance"]), 69)
        self.assertTrue(all(r["clauses"] for r in data["declarations"]))
        self.assertFalse(data["scope_complete"])
        self.assertIsNone(data["score"])
        # The former draft omitted this transitive edge from increment users.
        helper = next(r for r in data["declarations"] if r["id"] == "Tms.Term.binopI")
        self.assertIn("Tms.Term.binopC", helper["source_helper_references"])
        summary = next(r for r in data["declarations"] if r["id"] == "kernelSummary?")
        self.assertEqual(summary["source_helper_references"], ["fewNodes", "kernelNF", "summaryNodes"])
        normalizer = next(r for r in data["declarations"] if r["id"] == "kernelNF")
        self.assertIn("summaryNodes", normalizer["source_helper_references"])


class InventoryVersionCleanupControls(unittest.TestCase):
    def test_timeout_requires_confirmed_owned_container_removal(self):
        with tempfile.TemporaryDirectory() as tmp:
            with patch("check_candidate_inventory.bounded.headroom", return_value={}), patch("check_candidate_inventory.subprocess.run", side_effect=subprocess.TimeoutExpired("owned-version-probe", 30)), patch("check_candidate_inventory.bounded.remove_owned", return_value=True) as cleanup:
                with self.assertRaises(ValueError): audit.version_probe(Path(tmp))
                self.assertTrue(cleanup.call_args.args[0].startswith("h28-inventory-version-"))
                self.assertTrue((Path(tmp) / "versions.json").is_file())

    def test_uncertain_cleanup_stops_before_any_further_work(self):
        with tempfile.TemporaryDirectory() as tmp:
            with patch("check_candidate_inventory.bounded.headroom", return_value={}), patch("check_candidate_inventory.subprocess.run", side_effect=subprocess.TimeoutExpired("owned-version-probe", 30)), patch("check_candidate_inventory.bounded.remove_owned", return_value=False):
                with self.assertRaises(audit.bounded.CleanupError): audit.version_probe(Path(tmp))
