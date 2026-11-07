"""Reject stale waits, evidence inflation and permission expansion; no Lean."""
import copy,importlib.util,json,pathlib,sys,unittest
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[4]
s=importlib.util.spec_from_file_location("receipt",ROOT/"scripts/h62/item6/migrate-roadmap/producer_receipt.py")
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
class Controls(unittest.TestCase):
    def relay(self):return json.loads((ROOT/"tests/h62/item6/migrate-roadmap/contracts-mrs-h71-relay.json").read_text())
    def test_reported_current_blocker_accepted(self):m.validate_h71(self.relay())
    def test_obsolete_hash_wait_rejected(self):
        d=self.relay();d["current_import_closure_blocker"]="B-MIGRATION-HASH"
        with self.assertRaises(ValueError):m.validate_h71(d)
    def test_secondary_relay_not_independent_evidence(self):
        d=self.relay();d["independently_reproduced_by_mrs"]=True
        with self.assertRaises(ValueError):m.validate_h71(d)
    def test_isolated_hash_clearance_not_full_gate(self):
        d=self.relay();d["hash_clearance"]["full_migration_gate_complete"]=True
        with self.assertRaises(ValueError):m.validate_h71(d)
    def test_original_file_permission_not_inferred(self):
        d=self.relay();d["permissions"]["grants_original_file_edit"]=True
        with self.assertRaises(ValueError):m.validate_h71(d)
    def test_checkedsub_agreement_not_inferred(self):
        d=self.relay();d["permissions"]["grants_CheckedSub_application_agreement"]=True
        with self.assertRaises(ValueError):m.validate_h71(d)
    def test_secondary_relay_cannot_claim_guard_cleared(self):
        d=self.relay();d["observed_axioms_as_reported"]=[]
        with self.assertRaises(ValueError):m.validate_h71(d)
    def test_empty_trust_policy_not_relaxed(self):
        d=self.relay();d["expected_axioms"]=["propext"]
        with self.assertRaises(ValueError):m.validate_h71(d)
if __name__=="__main__":unittest.main()
