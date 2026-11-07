"""Regression checks against false completion and owner overclaim."""
import json
from pathlib import Path
import sys
import unittest
import subprocess
import tempfile
import os

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts/h62/item2/audit-bytecode-selection"))
from census import declarations
import inventory_report as report
import verify
import witness_ledger
from unittest.mock import patch
from elaborated_census import TEMPLATE, manifest_sha256
import hashlib


class InventoryTests(unittest.TestCase):
    def pins(self):
        data = {"base": report.BASE, "modules": ["Solidity.Backend.Selection.Interface"], "source_sha256": {"Solidity/Backend/Selection/Interface.lean": "0" * 64}}
        data["inspection_template_sha256"] = hashlib.sha256(TEMPLATE.encode()).hexdigest()
        data["manifest_sha256"] = manifest_sha256(data)
        return data

    def log(self, pins):
        row = {"name": "Fixture.field", "module": pins["modules"][0], "manifest_sha256": pins["manifest_sha256"]}
        done = {"manifest_sha256": pins["manifest_sha256"], "counts": {pins["modules"][0]: 1}}
        return "H62_CENSUS_JSON " + json.dumps(row) + "\nH62_CENSUS_DONE " + json.dumps(done) + "\n"

    def test_valid_complete_and_truncated(self):
        pins = self.pins()
        self.assertEqual(len(report.read_records(self.log(pins), pins)), 1)
        with self.assertRaisesRegex(ValueError, "completion"):
            report.read_records(self.log(pins).splitlines()[0], pins)

    def test_completed_zero_declaration_module(self):
        pins = self.pins()
        done = {"manifest_sha256": pins["manifest_sha256"], "counts": {pins["modules"][0]: 0}}
        self.assertEqual(report.read_records("H62_CENSUS_DONE " + json.dumps(done), pins), [])

    def test_old_inspector_log_cannot_match_new_algorithm(self):
        pins = self.pins()
        old_log = self.log(pins)
        pins["inspection_template_sha256"] = "3" * 64
        pins["manifest_sha256"] = manifest_sha256(pins)
        with self.assertRaisesRegex(ValueError, "manifest"):
            report.read_records(old_log, pins)

    def test_inspection_error_rejected(self):
        pins = self.pins()
        with self.assertRaisesRegex(ValueError, "diagnostic"):
            report.read_records(self.log(pins) + "fixture:1:1: error: failure\n", pins)

    def test_smaller_log_cannot_claim_larger_manifest(self):
        pins = self.pins()
        old_log = self.log(pins)
        pins["modules"].append("Solidity.Backend.Selection.Premises")
        pins["source_sha256"]["Solidity/Backend/Selection/Premises.lean"] = "1" * 64
        pins["manifest_sha256"] = manifest_sha256(pins)
        with self.assertRaisesRegex(ValueError, "manifest"):
            report.read_records(old_log, pins)

    def test_unpinned_or_duplicate_module_rejected(self):
        for duplicate in [False, True]:
            pins = self.pins()
            pins["modules"].append(pins["modules"][0] if duplicate else "Solidity.Backend.Selection.Premises")
            pins["manifest_sha256"] = manifest_sha256(pins)
            with self.assertRaisesRegex(ValueError, "module/source"):
                report.validate_pins(pins, pins["source_sha256"])

    def test_duplicate_declaration_rejected(self):
        pins = self.pins()
        row = self.log(pins).splitlines()[0]
        done = {"manifest_sha256": pins["manifest_sha256"], "counts": {pins["modules"][0]: 2}}
        with self.assertRaisesRegex(ValueError, "duplicate"):
            report.read_records(row + "\n" + row + "\nH62_CENSUS_DONE " + json.dumps(done), pins)

    def test_default_verifier_roster_covers_all_audit_lean_files(self):
        actual = {str(path.relative_to(ROOT)) for path in Path(__file__).parent.glob("*.lean")}
        self.assertEqual(set(verify.DEFAULT_ROOTS), actual)

    def test_quoted_audit_import_and_path_escape_rejection(self):
        self.assertEqual(verify.import_path("tests.h62.item2.«audit-bytecode-selection».RuntimePremiseWitness"),
                         "tests/h62/item2/audit-bytecode-selection/RuntimePremiseWitness.lean")
        for bad in ["A..B", "A.«../B»", "A.«B.C»", "A.«two words»"]:
            with self.assertRaises(ValueError):
                verify.import_path(bad)

    def test_exit_zero_without_output_fails_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "tests").mkdir()
            (root / "tests/Toy.lean").write_text("theorem toy : True := True.intro\n")
            runner = root / "fake-lean"
            runner.write_text("#!/bin/sh\nexit 0\n")
            runner.chmod(0o700)
            result = subprocess.run([sys.executable, str(ROOT / "scripts/h62/item2/audit-bytecode-selection/verify.py"),
                                     "--repo", str(root), "--root", "tests/Toy.lean", "--lean", str(runner),
                                     "--evidence", str(root / "evidence")],
                                    capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            journal = json.loads((root / "evidence/verification.json").read_text())
            self.assertEqual(journal[0]["exit"], 0)
            self.assertIsNone(journal[0]["output_sha256"])
            self.assertNotIn("AUDIT_FILES_SOURCE_CHECK_PASS", result.stdout)

    def test_private_unicode_source_mapping_and_generated_auxiliary(self):
        source = "namespace M\nprivate theorem café (n : Nat) : True := True.intro\nend M\n"
        candidate = declarations(source)[0]
        self.assertEqual(candidate["name_line"], 2)
        self.assertEqual(candidate["name_column"], len("private theorem "))
        row = {"kind": "theorem", "is_theorem": True, "private": True,
               "name": "_private.M.0.M.café", "user_name": "M.café",
               "declaration_range": {"selection_line": candidate["name_line"], "selection_column": candidate["name_column"]}}
        auxiliary = dict(row, name="_private.M.0.M.café._proof_1", user_name="M.café._proof_1")
        result = report.source_links([row, auxiliary], [candidate])
        self.assertEqual(result[0]["mapping_status"], "unique")
        self.assertEqual(row["source_origin"], "private_source_theorem")
        self.assertEqual(auxiliary["source_match_count"], 0)
        duplicate = dict(row, name="_private.M.1.M.café")
        result = report.source_links([row, duplicate], [candidate])
        self.assertEqual(result[0]["mapping_status"], "ambiguous")
        self.assertTrue(all(r["source_origin"] == "ambiguous_source_match" for r in [row, duplicate]))
        with self.assertRaisesRegex(ValueError, "duplicate source candidate"):
            report.source_links([row], [candidate, candidate])

    def test_multibyte_attribute_before_name_uses_codepoint_columns(self):
        source = "@[café] theorem t : True := True.intro"
        candidate = declarations(source)[0]
        self.assertEqual(candidate["name_column"], len("@[café] theorem "))
        self.assertNotEqual(candidate["name_column"], len("@[café] theorem ".encode()))

    def test_wrong_selection_position_stays_unmatched(self):
        candidate = declarations("theorem t : True := True.intro")[0]
        row = {"kind": "theorem", "is_theorem": True, "name": "t", "user_name": "t",
               "declaration_range": {"selection_line": 1, "selection_column": candidate["name_column"] + 1}}
        result = report.source_links([row], [candidate])
        self.assertEqual(result[0]["mapping_status"], "unmatched")
        self.assertEqual(row["source_match_count"], 0)

    def test_writer_exclusion_honored(self):
        path = "Solidity/Backend/Selection/Interface.lean"
        item = {"id": "fixture", "owner": "fixture-owner", "writeScope": "Solidity/Backend/**", "writeExclusions": path}
        self.assertEqual(report.owner_matches(path, [item]), [])


class WitnessLedgerTests(unittest.TestCase):
    def test_checked_links_and_tampered_evidence(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "fixture.olean"
            output.write_bytes(b"fixture output; this test does not assert Lean acceptance")
            log = Path(temporary) / "fixture.log"
            log.write_text("".join("'" + witness_ledger.NAMESPACE + helper + "' depends on axioms: [propext]\n"
                                   for _, helper, _ in witness_ledger.LINKS))
            inventory = {"base": report.BASE, "records": [{"name": target, "is_theorem": True}
                                                          for target, _, _ in witness_ledger.LINKS]}
            check = {"path": witness_ledger.HELPER_PATH, "exit": 0, "stop": None,
                     "source_unchanged_during_check": True,
                     "source_sha256": witness_ledger.sha(ROOT / witness_ledger.HELPER_PATH),
                     "command": ["fixture", "-o", str(output)], "output_sha256": witness_ledger.sha(output), "log": str(log)}
            rows = witness_ledger.link(inventory, [check], ROOT)
            self.assertEqual(sum(row["coverage"].startswith("simultaneous") for row in rows), 4)
            self.assertEqual(sum(row["coverage"].startswith("intentional") for row in rows), 1)
            self.assertTrue(all(not row["witness"]["establishes_original_conclusion"] for row in rows))
            group = (witness_ledger.HELPER_PATH, witness_ledger.NAMESPACE, witness_ledger.LINKS)
            with self.assertRaisesRegex(ValueError, "duplicate witness target across groups"):
                witness_ledger.link(inventory, [check], ROOT, groups=[group, group])
            original_mask = witness_ledger.mask
            for target, helper, negative in witness_ledger.LINKS:
                for operator in [" → True", " ∨ True"]:
                    def changed_mask(text, target=target, negative=negative, operator=operator):
                        clean = original_mask(text)
                        token = target + (")" if negative else "")
                        return clean.replace(token + " :=", token + operator + " :=", 1)
                    with patch.object(witness_ledger, "mask", side_effect=changed_mask):
                        with self.assertRaisesRegex(ValueError, "linkage mismatch"):
                            witness_ledger.link(inventory, [check], ROOT)
            with self.assertRaisesRegex(ValueError, "source check"):
                witness_ledger.link(inventory, [dict(check, source_sha256="0" * 64)], ROOT)
            output.write_bytes(b"changed")
            with self.assertRaisesRegex(ValueError, "output check"):
                witness_ledger.link(inventory, [check], ROOT)
            output.write_bytes(b"fixture output; this test does not assert Lean acceptance")
            log.write_text(log.read_text().replace("[propext]", "[unapprovedAxiom]"))
            with self.assertRaisesRegex(ValueError, "unexpected helper axiom"):
                witness_ledger.link(inventory, [check], ROOT)
            inventory["records"].append(inventory["records"][0])
            with self.assertRaisesRegex(ValueError, "duplicate"):
                witness_ledger.link(inventory, [check], ROOT)


if __name__ == "__main__":
    unittest.main()
