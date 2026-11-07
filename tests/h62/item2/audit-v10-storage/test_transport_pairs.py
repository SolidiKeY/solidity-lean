"""Guard source/version observations being promoted to H57 proof transport."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("transport_pairs", ROOT / "scripts/h62/item2/audit-v10-storage/transport_pairs.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)

class TransportPairControls(unittest.TestCase):
    def setUp(self):
        self.pins = json.loads((ROOT / m.PINS).read_bytes())
        self.old = {"signature_sha256": "old", "variable_context": [], "visibility": "public"}
        self.now = dict(self.old, signature_sha256="new")
        self.pin = {"file": "Solidity/A.lean", "source_name": "A.t", "kind": "H19-balance-domain",
            "original_signature_sha256": "old", "original_context_sha256": m.context(self.old),
            "observed_signature_sha256": "new", "observed_context_sha256": m.context(self.now)}

    def test_exact_pair_is_never_transport(self):
        row = m.join_pair(self.pin, self.old, self.now)
        self.assertTrue(row["current_matches_recorded_observation"])
        self.assertIsNone(row["transport_proof"]["reference"])
        self.assertFalse(row["original_obligation_discharged"])

    def test_original_drift_fails_closed(self):
        for old in [None, dict(self.old, signature_sha256="forged"), dict(self.old, variable_context=["variable (h : False)"])]:
            with self.assertRaises(ValueError): m.join_pair(self.pin, old, self.now)

    def test_current_drift_or_missing_remains_accounted(self):
        for now in [None, dict(self.now, signature_sha256="changed"), dict(self.now, visibility="private")]:
            row = m.join_pair(self.pin, self.old, now)
            self.assertFalse(row["current_matches_recorded_observation"])
            self.assertEqual(row["source_name"], "A.t")
            self.assertFalse(row["original_obligation_discharged"])

    def test_membership_duplicate_and_traversal_rejected(self):
        m.validate_pins(self.pins)
        bad = copy.deepcopy(self.pins); bad["cases"].pop()
        with self.assertRaises(ValueError): m.validate_pins(bad)
        bad = copy.deepcopy(self.pins); bad["cases"][1] = bad["cases"][0]
        with self.assertRaises(ValueError): m.validate_pins(bad)
        bad = copy.deepcopy(self.pins); bad["cases"][0]["file"] = "Solidity/../outside.lean"
        with self.assertRaises(ValueError): m.validate_pins(bad)

if __name__ == "__main__": unittest.main()
