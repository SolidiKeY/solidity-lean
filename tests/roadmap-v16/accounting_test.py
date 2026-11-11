#!/usr/bin/env python3
"""Negative controls against live Lean/G03 inventory; no Lean invocation."""
import copy, importlib.util, json, pathlib, sys, unittest, tempfile
sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("v16_accounting", ROOT/"scripts/roadmap-v16-accounting.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
DATA = None

class AccountingTests(unittest.TestCase):
    def setUp(self):
        self.inv = copy.deepcopy(DATA["inventory"])
        self.report = copy.deepcopy(DATA["report"])
        self.ledger = json.loads((ROOT/m.LEDGER).read_text())
    def invalid_report(self):
        with self.assertRaises(m.Invalid): m.validate_report(self.report,self.inv,self.ledger)
    def invalid_inventory(self):
        with self.assertRaises(m.Invalid): m.validate_inventory(self.inv)
    def test_callback_control_claim(self):
        m.validate_claims([{ "id":"callback-success", "theorem":"Solidity.Roadmap.V16.CallbackControls.nil_callback_post", "kind":"witness"}], self.inv)
    def test_live_report(self):
        m.validate_inventory(self.inv);m.validate_report(self.report,self.inv,self.ledger)
    def test_nested_owned_module_cannot_escape(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=pathlib.Path(tmp);p=root/"Solidity/Roadmap/V16/Nested/Only.lean"
            p.parent.mkdir(parents=True);p.write_text("-- owned fixture, no execution semantics\n")
            discovered=m.sources(root)
            self.assertIn("Solidity/Roadmap/V16/Nested/Only.lean",discovered)
            fake=dict(self.inv,sources=discovered)
            with self.assertRaises(m.Invalid):m.validate_owned_imports(fake)
            fake["modules"]=["Solidity.Roadmap.V16.Nested.Only"]
            m.validate_owned_imports(fake)
    def test_relocated_owned_module_cannot_escape(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=pathlib.Path(tmp);p=root/"Solidity/Examples/Roadmap/V16/Only.lean"
            p.parent.mkdir(parents=True);p.write_text("namespace Solidity.Roadmap.V16 end Solidity.Roadmap.V16\n")
            discovered=m.sources(root)
            self.assertIn(str(p.relative_to(root)),discovered)
            with self.assertRaises(m.Invalid):
                m.validate_owned_imports({"sources":discovered,"modules":[]})

    def test_absent_imported_module(self):self.inv["modules"].pop();self.invalid_inventory()
    def test_absent_constructor_obligation(self):
        self.report["obligations"]=[r for r in self.report["obligations"] if r["id"]!="constructor:Solidity.Stmt.assign"]
        self.invalid_report()
    def test_absent_actual_constructor(self):
        p=next(p for p in self.inv["inductives"] if p["name"]=="Solidity.Stmt")
        p["constructors"].pop();self.invalid_inventory()
    def test_absent_combination(self):
        self.report["obligations"]=[r for r in self.report["obligations"] if r["id"]!="combination:0"]
        self.invalid_report()
    def test_contradictory_duplicate(self):
        self.report["obligations"].append(dict(self.report["obligations"][0],status="closed"));self.invalid_report()
    def test_premise_only_claim(self):
        n="Solidity.Roadmap.V16.decoded_invariant"
        t=next(t for t in self.inv["theorems"] if t["name"]==n)
        self.assertIn("assumed-PublicCorrectness",m.theorem_obligations(t))
        with self.assertRaises(m.Invalid):m.validate_claims([{"id":"G49","theorem":n,"kind":"closed"}],self.inv)
    def test_residual_domain_explicit(self):
        t=next(t for t in self.inv["theorems"] if t["name"]=="Solidity.Roadmap.V16.completion_at_need")
        self.assertIn("undischarged-pass-domain",m.theorem_obligations(t))
    def test_generic_claim_does_not_close(self):
        n="Solidity.Roadmap.V16.decoded_invariant"
        self.assertTrue(m.validate_claims([{"id":"generic:test","theorem":n,"kind":"generic"}],self.inv))
        self.assertFalse(self.report["laneComplete"])
        self.assertTrue(all(r["status"]=="open" for r in self.report["obligations"]))
    def test_absent_theorem_claim(self):
        with self.assertRaises(m.Invalid):m.validate_claims([{"id":"x","theorem":"invented","kind":"generic"}],self.inv)
    def test_contradictory_claims(self):
        n=self.inv["theorems"][0]["name"]
        with self.assertRaises(m.Invalid):m.validate_claims([{"id":"x","theorem":n,"kind":"generic"},{"id":"x","theorem":n,"kind":"witness"}],self.inv)
    def test_wrong_base(self):self.inv["base"]="0"*40;self.invalid_inventory()
    def test_wrong_head(self):self.inv["head"]="0"*40;self.invalid_inventory()
    def test_wrong_ledger(self):self.inv["ledgerSha256"]="0"*64;self.invalid_inventory()
    def test_absent_statement(self):self.report["theorems"].pop();self.invalid_report()
    def test_altered_actual_statement(self):self.inv["theorems"][0]["type"]="True";self.invalid_inventory()
    def test_altered_axiom_output(self):self.inv["theorems"][0]["axioms"]=["sorryAx"];self.invalid_inventory()
    def test_erased_prerequisites(self):self.report["openPremises"]=[];self.invalid_report()
    def test_premise_only_witness(self):
        with self.assertRaises(m.Invalid):m.validate_claims([{"id":"x","theorem":"Solidity.Roadmap.V16.decoded_invariant","kind":"witness"}],self.inv)
    def test_altered_boundary(self):self.report["boundary"]="full source compiler correctness established";self.invalid_report()
    def test_unbound_old_log(self):
        with tempfile.TemporaryDirectory() as tmp:
            old=pathlib.Path(tmp)/"unbound.log"
            old.write_text("V16-INVENTORY "+json.dumps({k:self.inv[k] for k in ["inductives","theorems"]})+"\nexit=0\n")
            with self.assertRaises(m.Invalid):m.snapshot(old)
    def test_stale_resnapshot(self):
        old=m.current_binding
        def changed(root=m.ROOT):
            b=old(root);b["head"]="0"*40;return b
        try:
            m.current_binding=changed
            with self.assertRaises(m.Invalid):m.snapshot(self.inv["rawLogPath"])
        finally:m.current_binding=old
    def test_unapproved_extra_claim_fields(self):
        n=self.inv["theorems"][0]["name"]
        with self.assertRaises(m.Invalid):m.validate_claims([{"id":"x","theorem":n,"kind":"generic","closed":True}],self.inv)
    def test_false_lane_completion(self):self.report["laneComplete"]=True;self.invalid_report()

if __name__=="__main__":
    DATA=json.loads(pathlib.Path(sys.argv[1]).read_text());unittest.main(argv=[sys.argv[0]],verbosity=2)
