"""Guard against missing root paths or unsupported syntax falsely certifying API coverage.

Regression: an unsupported declaration must remain an explicit gap; configuration
coverage and unchanged source must never replace generated compiler exports.
"""
import importlib.util
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[4]

def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT/"scripts/h62/item6/migrate-root-gate"/filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

root = load("root_inventory", "root-api-inventory.py")
scanner = load("root_scanner", "public-api-inventory.py")

class RootCoverageControls(unittest.TestCase):
    def test_missing_duplicate_or_extra_root_input_is_rejected(self):
        expected = root.scope()
        valid = [{"path": p} for p in expected]
        root.validate_coverage(expected, valid)
        for bad in [valid[:-1], valid+[valid[0]], valid+[{"path": "Outside.lean"}]]:
            with self.assertRaises(ValueError):
                root.validate_coverage(expected, bad)

    def test_unsupported_header_is_gap_not_empty_export(self):
        result = root.lexical(b"opaque hidden : Nat\ndef later : Nat := 1\n", scanner)
        self.assertFalse(result["header_capture_complete_for_supported_grammar"])
        self.assertIn("unsupported", result["error"])
        self.assertIn("no zero-declaration", result["limitation"])

    def test_generated_family_header_is_only_lexical_evidence(self):
        result = root.lexical(b"inductive Item where\n | value : Item\n", scanner)
        self.assertEqual(result["headers"], ["inductive Item"])
        self.assertIn("not elaborated", result["limitation"])
        self.assertNotIn("public_exports", result)

if __name__ == "__main__":
    unittest.main()
