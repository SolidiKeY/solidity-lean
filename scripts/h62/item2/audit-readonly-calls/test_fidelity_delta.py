import copy
import importlib.util
from pathlib import Path
import unittest
spec=importlib.util.spec_from_file_location("fidelity",Path(__file__).with_name("fidelity_delta.py"))
fidelity=importlib.util.module_from_spec(spec);spec.loader.exec_module(fidelity)


class FidelityControls(unittest.TestCase):
    def setUp(self):
        self.rows=[dict(file="A.lean",source_name=n,signature_sha256="same",variable_context=["variable {E : Env}"],visibility="private" if n=="private_helper" else "public",witness_status="pending",owner="RO") for n in ("private_helper","public_consumer")]

    def test_removed_private_still_counts_once(self):
        result=fidelity.compare(self.rows,self.rows[1:])
        self.assertEqual(result["original_declarations"],2)
        self.assertEqual(len(result["original_obligations"]),2)
        self.assertEqual(result["source_statuses"],{"absent-upstream":1,"lexical-header-retained":1})
        self.assertTrue(all(r["original_audit_status"]=="pending" for r in result["original_obligations"]))

    def test_same_header_with_changed_implicit_context_is_drift(self):
        current=copy.deepcopy(self.rows);current[0]["variable_context"]=["variable {E : OtherEnv}"]
        self.assertEqual(fidelity.compare(self.rows,current)["source_statuses"]["header-or-context-drift"],1)

    def test_new_or_renamed_decl_does_not_discharge_missing_original(self):
        current=copy.deepcopy(self.rows);current[0]["source_name"]="new_helper"
        result=fidelity.compare(self.rows,current)
        self.assertEqual(result["source_statuses"]["absent-upstream"],1)
        self.assertEqual(result["added_declarations"],[{"file":"A.lean","source_name":"new_helper"}])

    def test_duplicate_original_or_current_is_rejected(self):
        for old,new in [(self.rows+self.rows,self.rows),(self.rows,self.rows+self.rows)]:
            with self.assertRaisesRegex(ValueError,"duplicate"):
                fidelity.compare(old,new)


if __name__=="__main__":unittest.main()
