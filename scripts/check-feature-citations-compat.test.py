#!/usr/bin/env python3
"""Reader compatibility at the assigned base, including unchanged validation."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]
BASE = "a0a9ca15ba35fd6e8d9a9be10e4b6b45dbf45d3e"
spec = importlib.util.spec_from_file_location("feature_audit", ROOT / "scripts/solidity-feature-audit.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class ReaderCompatibility(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = json.loads(subprocess.check_output(
            ["git", "show", BASE + ":docs/solidity-features.json"], cwd=ROOT, text=True))
        cls.new = json.loads((ROOT / "docs/solidity-features.json").read_text())
        cls.ledger = json.loads(audit.LEDGER.read_text())

    def test_old_manifest_validates(self):
        self.assertEqual(self.old["schemaVersion"], 1)
        audit.validate(self.old, self.ledger)

    def test_new_manifest_validates(self):
        self.assertEqual(self.new["schemaVersion"], 2)
        self.assertTrue(all(isinstance(r["theorems"], list) for r in self.new["features"]))
        audit.validate(self.new, self.ledger)

    def test_citation_extension_preserves_reader_rendering(self):
        # Isolate citation fields from future authorized status/evidence edits.
        old = copy.deepcopy(self.old)
        extended = copy.deepcopy(old)
        extended["schemaVersion"] = 2
        for row in extended["features"]:
            row["theorems"] = []
        for render in (audit.render_lean, audit.render_lean_info, audit.render_report):
            self.assertEqual(render(old), render(extended))

    def test_other_versions_rejected(self):
        for version in (0, 3, "2", None):
            with self.subTest(version=version):
                data = copy.deepcopy(self.new)
                data["schemaVersion"] = version
                with self.assertRaises(AssertionError):
                    audit.validate(data, self.ledger)

    def test_existing_evidence_validation_preserved(self):
        for original in (self.old, self.new):
            data = copy.deepcopy(original)
            data["features"][0]["localEvidence"] = ["missing-citation-control"]
            with self.assertRaises(AssertionError):
                audit.validate(data, self.ledger)


if __name__ == "__main__":
    unittest.main(verbosity=2)
