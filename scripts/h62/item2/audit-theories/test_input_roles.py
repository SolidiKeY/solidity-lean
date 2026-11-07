import unittest
from copy import deepcopy
from input_roles import SPECS,annotate

class RoleCompletenessTests(unittest.TestCase):
    def row(self,name):
        spec=SPECS[name]
        return {"source_name":name,"file":"fixture","source_header":"fixture",
          "elaborated_type_sha256":"fixture","documented_producing_lane":"fixture",
          "elaborated":{"binders":[{"name":b,"type":"fixture","is_prop":b in spec["premises"]}for b in spec["binders"]]}}
    def test_post_premise_input_cannot_disappear(self):
        name="Solidity.Theory.Progress.Ends.notStuck";row=self.row(name)
        row["elaborated"]["binders"].pop() # drops w AFTER the logical h premise
        with self.assertRaisesRegex(AssertionError,"ordered binder census"):
            annotate(row,SPECS[name])
    def test_universal_NS_premise_cannot_be_unclassified(self):
        name="Solidity.Theory.Progress.NS.ends";spec=deepcopy(SPECS[name])
        spec["premises"]={}
        with self.assertRaisesRegex(AssertionError,"premise role omitted"):
            annotate(self.row(name),spec)

if __name__=="__main__":unittest.main()
