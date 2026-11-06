import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location("selector",ROOT/"scripts/roadmap-v17-selector-contract.py")
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)


class SetupLint(unittest.TestCase):
    def setUp(self):
        self.closure={"Solidity.KeySort":{"path":"Solidity/KeySort.lean","sha256":"a"*64}}
        self.parts=["/private/KeySort.olean","/private/KeySort.ir","/private/KeySort.olean.server","/private/KeySort.olean.private"]
        self.setup={"name":"_unknown","isModule":False,"options":{},"plugins":[],"dynlibs":[],"importArts":{"Solidity.KeySort":self.parts}}
        self.hashes={p:"b"*64 for p in self.parts}

    def test_part_roles_not_loaded_authentication(self):
        r=s.lint_setup(self.setup,self.closure,self.hashes,self.hashes)
        self.assertEqual(r["legacyPrivateLevelParts"]["Solidity.KeySort"]["oleanParts"],[self.parts[0],self.parts[2],self.parts[3]])
        self.assertEqual(r["legacyPrivateLevelParts"]["Solidity.KeySort"]["evaluatorIR"],self.parts[1])
        self.assertFalse(r["selectorsAuthenticated"]);self.assertFalse(r["kernelValidated"])

    def test_missing_ir_and_changed_inputs(self):
        bad=dict(self.hashes);bad.pop(self.parts[1])
        with self.assertRaisesRegex(ValueError,"unbound selected"):s.lint_setup(self.setup,self.closure,bad,bad)
        bad=dict(self.hashes);bad[self.parts[0]]="c"*64
        with self.assertRaisesRegex(ValueError,"changed before/after"):s.lint_setup(self.setup,self.closure,self.hashes,bad)

    def test_wrong_part_roles_and_path(self):
        for path in ("/private/../KeySort.olean","relative.olean"):
            bad=copy.deepcopy(self.setup);bad["importArts"]["Solidity.KeySort"][0]=path
            with self.assertRaises(ValueError):s.lint_setup(bad,self.closure,self.hashes,self.hashes)
        bad=copy.deepcopy(self.setup);bad["importArts"]["Solidity.KeySort"][1]=self.parts[2]
        with self.assertRaisesRegex(ValueError,"part role"):s.lint_setup(bad,self.closure,self.hashes,self.hashes)

    def test_missing_selector_override_or_plugin(self):
        for change in ({"importArts":{}},{"plugins":["x"]},{"options":{"x":True}},{"isModule":True},{"imports?":[]}):
            bad=copy.deepcopy(self.setup);bad.update(change)
            with self.assertRaises(ValueError):s.lint_setup(bad,self.closure,self.hashes,self.hashes)

    def test_empty_closure_cannot_match(self):
        empty=copy.deepcopy(self.setup);empty["importArts"]={}
        with self.assertRaisesRegex(ValueError,"empty/oversized"):s.lint_setup(empty,{}, {}, {})

    def test_lookup_receipt_cannot_be_setup(self):
        with self.assertRaises(ValueError):s.lint_setup({"objects":{},"selectorsAuthenticated":False},self.closure,{}, {})

    def test_no_empty_replay_intent(self):
        with self.assertRaisesRegex(ValueError,"missing original request"):s.original_request_consistency({}, {})


@unittest.skipUnless(os.environ.get("V17_SELECTOR_PLANS"),"actual sealed request inputs not supplied")
class ActualContracts(unittest.TestCase):
    def setUp(self):
        w=Path(os.environ["V17_SELECTOR_PLANS"])
        self.raw=(w/"request-a-final/LOCAL-DIAGNOSTIC-REQUEST.json").read_bytes();self.digest=hashlib.sha256(self.raw).hexdigest()
        self.plan=s.pinned_plan(self.raw,self.digest);self.graph=json.loads((w/"a-source-result.json").read_text())

    def test_actual_groups_pending_no_generic_promotion(self):
        r=s.prepare(self.plan,self.graph,self.digest,"f"*64)
        self.assertEqual(sum(len(q["request"]["declarations"]) for q in r["queries"]),18)
        self.assertEqual(len(r["foundationMetadataRequest"]),25)
        self.assertTrue(r["budgetHold"]["originalLocalBudgetExhausted"])
        self.assertFalse(r["budgetHold"]["additionalSharedSecondsApproved"])
        self.assertFalse(r["reportedFirstOutcome"]["completedMetadata"])
        self.assertFalse(r["existingConsumerCompatibility"]["genericKernelVerify"])
        self.assertFalse(r["selectorsAuthenticated"]);self.assertFalse(r["replayVerified"])
        self.assertTrue(all(q["selectorModeChangeRequiresNewFirst"] and not q["appliesAsReplayOfOriginalNoSetupRun"] for q in r["queries"]))
        self.assertTrue(all(any(arg.startswith("--setup=") for arg in q["explicitSelectionQueryArgv"]) for q in r["queries"]))

    def test_wrong_request_digest_budget_and_promotion(self):
        with self.assertRaisesRegex(ValueError,"digest"):s.pinned_plan(self.raw,"0"*64)
        for key,value in (("componentCumulativeSeconds",301),("leanJobs",True)):
            bad=copy.deepcopy(self.plan);bad["limits"][key]=value;raw=json.dumps(bad).encode()
            with self.assertRaises(ValueError):s.pinned_plan(raw,hashlib.sha256(raw).hexdigest())
        bad=copy.deepcopy(self.plan);bad["kernelValidated"]=True;raw=json.dumps(bad).encode()
        with self.assertRaises(ValueError):s.pinned_plan(raw,hashlib.sha256(raw).hexdigest())

    def test_empty_duplicate_groups_and_filenames(self):
        for mode in ("empty","duplicate","filename"):
            bad=copy.deepcopy(self.plan)
            if mode=="empty":bad["queries"]=[]
            elif mode=="duplicate":bad["queries"].append(bad["queries"][0])
            else:bad["queries"][0]["axioms"]=bad["queries"][0]["query"]
            raw=json.dumps(bad).encode()
            with self.subTest(mode=mode),self.assertRaises(ValueError):s.pinned_plan(raw,hashlib.sha256(raw).hexdigest())

    def test_missing_or_wrong_source_graph(self):
        bad=copy.deepcopy(self.graph);module=self.plan["queries"][0]["request"]["module"]
        bad["modules"][module]["sha256"]="0"*64
        with self.assertRaises(ValueError):s.query_closure(self.plan,bad,module)
        bad=copy.deepcopy(self.graph);bad["modules"].pop(module)
        with self.assertRaises(KeyError):s.query_closure(self.plan,bad,module)

    def test_native_selector_fields_not_silently_ignored(self):
        for key in ("setup","argv","env","actualInputs"):
            bad=copy.deepcopy(self.plan);bad[key]={}
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,"not original requests"):
                s.original_request_consistency(bad,bad)
        bad=copy.deepcopy(self.plan);bad["newUnknownField"]=1
        with self.assertRaises(ValueError):s.original_request_consistency(self.plan,bad)

    def test_typed_after_source_cannot_be_replay(self):
        self.assertTrue(s.original_request_consistency(self.plan,self.plan)["originalRequestInputsConsistent"])
        bad=copy.deepcopy(self.plan);path=next(iter(bad["sourceFiles"]));bad["sourceFiles"][path]="0"*64
        with self.assertRaisesRegex(ValueError,"changed complete original"):s.original_request_consistency(self.plan,bad)
        bad=copy.deepcopy(self.plan);bad["queries"][0]["request"]["declarations"].pop()
        with self.assertRaises(ValueError):s.original_request_consistency(self.plan,bad)


if __name__=="__main__":unittest.main()
