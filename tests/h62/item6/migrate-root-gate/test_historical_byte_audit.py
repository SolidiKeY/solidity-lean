"""Guard H30/H86 against accepting current copies or locator normalization as historical bytes."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("historical_audit",ROOT/"scripts/h62/item6/migrate-root-gate/historical-byte-audit.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)

class HistoricalIdentityControls(unittest.TestCase):
    def test_current_copy_and_normalized_hint_never_certify_history(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory)/"old-api.json"
            p.write_text('{"regenerated":true}')
            for locator in [str(p),str(p)+"`:"]:
                row = audit.classify(locator)
                self.assertEqual(row["current_candidate_kind"],"file")
                self.assertEqual(row["historical_exact_bytes"],"UNVERIFIABLE")
                self.assertFalse(row["historical_digest_verified"])
                self.assertFalse(row["normalization_is_identity_evidence"])
                self.assertFalse(row["API_axiom_acceptance"])
            missing = audit.classify(str(Path(directory)/"elsewhere"/p.name))
            self.assertEqual(missing["current_candidate_kind"],"missing")

    def test_existing_literal_filename_precedes_punctuation_hint(self):
        with tempfile.TemporaryDirectory() as directory:
            literal = Path(directory)/"old-api.json:"
            literal.write_text("historical-looking current bytes")
            row = audit.classify(str(literal))
            self.assertTrue(row["literal_exists"])
            self.assertFalse(row["candidate_exists"])
            self.assertEqual(row["looked_up_path"],str(literal))
            self.assertEqual(row["current_candidate_kind"],"file")
            self.assertEqual(row["historical_exact_bytes"],"UNVERIFIABLE")

    def test_directory_is_not_a_recovered_export(self):
        with tempfile.TemporaryDirectory() as directory:
            row = audit.classify(directory)
            self.assertEqual(row["current_candidate_kind"],"directory")
            self.assertNotIn("current_candidate_sha256",row)
            self.assertEqual(row["historical_exact_bytes"],"UNVERIFIABLE")

if __name__ == "__main__":
    unittest.main()
