import copy
import sys
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT / "scripts/h55/vectors-tables"))
import raw_case_labels as c

class RawCaseLabelTests(unittest.TestCase):
    def test_grouped_and_case_patterns(self):
        self.assertEqual(c.split_label("| .break_ _ | .continue_ _ => body","Lean.Parser.Tactic.inductionAlt"),[".break_ _",".continue_ _"])
        self.assertEqual(c.split_label("| .ok () => body","Lean.Parser.Term.matchAlt"),[".ok ()"])
        self.assertEqual(c.split_label("case nil => body","Lean.Parser.Tactic.case"),["case nil"])
        for bad in ["| x | => body","| x (y | z) => body","| x"]:
            with self.assertRaises(ValueError): c.split_label(bad,"Lean.Parser.Term.matchAlt")
    def test_missing_extra_order_and_schema(self):
        row={"kind":"Lean.Parser.Term.matchAlt","node_start":1,"node_end":2,"node_sha256":"a"*64,"declaration_start":0,"declaration_end":3,"declaration_sha256":"b"*64,"declaration_heading":"theorem a","pattern_index":0,"pattern":"x"}; second={**row,"pattern":"y"}
        data={"master":"a"*40,"alternative_nodes":2,"files":{"RawA.lean":[row,second]}}
        expected=c.summary(data)
        for label,rows in [("missing",[row]),("extra",[row,second,row]),("order",[second,row])]:
            with self.subTest(label=label):
                altered=copy.deepcopy(data); altered["files"]["RawA.lean"]=rows
                self.assertNotEqual(c.summary(altered),expected)
        altered=copy.deepcopy(data); altered["files"]["RawA.lean"][0]["extra"]=1
        with self.assertRaises(ValueError): c.summary(altered)

if __name__=="__main__": unittest.main()
