import copy
import importlib.util
from pathlib import Path
import unittest
s=importlib.util.spec_from_file_location("plan",Path(__file__).with_name("fixture_plan.py"))
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)

class PlanTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.classification=m.m.classify()
        cls.plan=m.build(cls.classification)
    def test_all_claims_and_support(self):
        m.validate(self.plan,self.classification)
        self.assertEqual(self.plan["totals"],dict(claims=1623,packets=84,private=616,public=1007))
    def test_corruption_refused(self):
        for name in ("drop","duplicate","contract","fixture","equivalence"):
            with self.subTest(name=name):
                y=copy.deepcopy(self.plan)
                if name=="drop":y["cases"].pop()
                elif name=="duplicate":y["cases"].append(y["cases"][0])
                elif name=="contract":y["cases"][0]["exact_result_type"]="True"
                elif name=="fixture":next(p for p in y["packets"] if p["fixture_ids"])["fixture_ids"].pop()
                else:y["cases"][0]["equivalence"]["proved"]=True
                with self.assertRaises(ValueError):m.validate(y,self.classification)

if __name__=="__main__":unittest.main()
