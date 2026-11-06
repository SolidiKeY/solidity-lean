import sys
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/h55/vectors-tables"))
import raw_semantic_ledger as ledger

class SemanticLedgerTests(unittest.TestCase):
    def test_declarations_schema_and_inventory(self):
        source="def holds : Prop := True\ntheorem example : True := by trivial\n"
        found=ledger.declarations(source)
        self.assertEqual(list(found),["holds","example"])
        self.assertEqual(found["example"]["statement"],"theorem example : True")
        with self.assertRaises(ValueError): ledger.declarations(source+"theorem example : True := by trivial\n")
        with self.assertRaises(ValueError): ledger.declarations("theorem example : True\n")
        logic=dict.fromkeys(["holds","formula",*ledger.LOGIC]); previous={"old":None}; current={**previous,**dict.fromkeys(ledger.FRAME)}
        ledger.validate_inventory(logic,current,previous)
        for label, bad_logic, bad_current in [("missing",{k:v for k,v in logic.items() if k!="holds"},current),("extra",{**logic,"extra":None},current),("frame",logic,previous)]:
            with self.subTest(label=label):
                with self.assertRaises(ValueError): ledger.validate_inventory(bad_logic,bad_current,previous)

if __name__ == "__main__": unittest.main()
