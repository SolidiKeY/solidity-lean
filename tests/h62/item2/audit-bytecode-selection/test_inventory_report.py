"""Regression checks against false completion and owner overclaim."""
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts/h62/item2/audit-bytecode-selection"))
import inventory_report as report
import verify
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

    def test_writer_exclusion_honored(self):
        path = "Solidity/Backend/Selection/Interface.lean"
        item = {"id": "fixture", "owner": "fixture-owner", "writeScope": "Solidity/Backend/**", "writeExclusions": path}
        self.assertEqual(report.owner_matches(path, [item]), [])


if __name__ == "__main__":
    unittest.main()
