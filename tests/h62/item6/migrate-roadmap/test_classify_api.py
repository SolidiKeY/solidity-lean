"""Fail-closed structural classification controls; no Lean execution."""
import copy,importlib.util,pathlib,sys,unittest
sys.dont_write_bytecode=True
p=pathlib.Path(__file__).resolve().parents[4]/"scripts/h62/item6/migrate-roadmap/classify_api.py"
s=importlib.util.spec_from_file_location("classification",p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
class Controls(unittest.TestCase):
    def row(self):return dict(universe_count=1,alpha=["forall","implicit",["sort",["param",0]],["bvar",0]],binder_erased=["forall","erased",["sort",["param",0]],["bvar",0]])
    def test_alpha_equal(self):self.assertEqual(m.classify(self.row(),self.row()),"alpha_only")
    def test_visibility_not_silently_accepted(self):
        a=self.row();b=copy.deepcopy(a);b["alpha"][1]="explicit"
        self.assertEqual(m.classify(a,b),"binder_visibility_only")
    def test_changed_domain_not_erased(self):
        a=self.row();b=copy.deepcopy(a);b["alpha"][2]=["const","Nat",[]];b["binder_erased"][2]=["const","Nat",[]]
        self.assertEqual(m.classify(a,b),"structural")
    def test_unused_universe_arity_is_api_change(self):
        a=self.row();b=copy.deepcopy(a);b["universe_count"]=2
        self.assertEqual(m.classify(a,b),"structural")
    def test_unsupported_metadata_rejects_even_when_identical(self):
        a=self.row();a["alpha"]=["unsupported-metadata",a["alpha"]]
        with self.assertRaises(ValueError):m.classify(a,a)
    def test_debruijn_index_change_detected(self):
        a=self.row();b=copy.deepcopy(a);b["alpha"][-1]=["bvar",1];b["binder_erased"][-1]=["bvar",1]
        self.assertEqual(m.classify(a,b),"structural")
    def test_constant_universe_index_change_detected(self):
        a=self.row();b=copy.deepcopy(a)
        a["alpha"]=a["binder_erased"]=["const","Eq",[["param",0]]]
        b["alpha"]=b["binder_erased"]=["const","Eq",[["param",1]]]
        self.assertEqual(m.classify(a,b),"structural")
    def test_constant_identity_change_detected(self):
        a=self.row();b=copy.deepcopy(a)
        a["alpha"]=a["binder_erased"]=["const","Nat",[]]
        b["alpha"]=b["binder_erased"]=["const","Int",[]]
        self.assertEqual(m.classify(a,b),"structural")
    def test_first_difference_points_to_changed_leaf(self):
        self.assertEqual(m.first_difference(["app",["bvar",0]],["app",["bvar",1]])["path"],[1,1])
if __name__=="__main__":unittest.main()
