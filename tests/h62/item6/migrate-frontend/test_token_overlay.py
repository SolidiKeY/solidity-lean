"""Missing declaration names must never satisfy frozen-type comparison."""
import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('token_overlay',ROOT/'scripts/h62/item6/migrate-frontend/token_overlay.py')
t=importlib.util.module_from_spec(spec);spec.loader.exec_module(t)
class TokenBindingControls(unittest.TestCase):
    def test_missing_from_both_is_rejected(self):
        self.assertEqual(t.selected_type_mismatches(['A'],{},{}),['A'])
    def test_missing_from_either_is_rejected(self):
        for old,new in (({'A':{}},{}),({}, {'A':{}})):
            self.assertEqual(t.selected_type_mismatches(['A'],old,new),['A'])
    def test_type_change_is_rejected(self):
        self.assertEqual(t.selected_type_mismatches(['A'],{'A':{'type':'Nat'}},{'A':{'type':'Int'}}),['A'])
    def test_axiom_changes_are_separate_from_type_comparison(self):
        self.assertEqual(t.selected_type_mismatches(['A'],{'A':{'type':'Nat','axioms':[]}},{'A':{'type':'Nat','axioms':['propext']}}),[])
if __name__=='__main__':unittest.main()
