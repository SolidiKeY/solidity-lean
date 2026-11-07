#!/usr/bin/env python3
"""Source dependency checks; no macro type inference or witness proof."""
import sys
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"scripts/h62/item2/audit-v09-passes"))
import macro_dependencies as audit
from premises import telescope,macro_heads

class MacroDependencyAcceptance(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result=audit.build(ROOT)

    def test_every_macro_caller_exactly_once(self):
        expected={r["name"] for r in audit.census(ROOT)["declarations"] if macro_heads(telescope(r["signature"])[1])}
        rows=self.result["rows"]
        self.assertEqual(len(rows),27)
        self.assertEqual({r["caller"] for r in rows},expected)
        self.assertEqual(self.result["summary"]["candidate_signature_text_equal"],27)

    def test_callee_source_spans_and_import_reachability(self):
        for row in self.result["rows"]:
            target=row["candidate"]
            source=audit.subprocess.check_output(["git","show",f"{audit.BASE}:{target['path']}"],cwd=ROOT).decode()
            a,b=target["character_span"]
            self.assertEqual(source[a:b].strip(),target["signature"])
            self.assertTrue(row["candidate_in_frozen_import_closure"])
            self.assertTrue(row["current_candidate_available_section_text_equal"])
            for group in row["candidate_available_section_variables"]:
                start,end=group["span"]
                self.assertEqual(source[start:end],group["source"])
            self.assertEqual(row["macro_heads"][0]["token"].split(".")[-1],target["name"].split(".")[-1])

    def test_no_extra_caller_premises_or_owner_claim(self):
        for row in self.result["rows"]:
            self.assertEqual(row["caller_new_premises"],[])
            self.assertIsNone(row["simultaneous_witness"])
            self.assertIn("pending",row["resolution"])
            if "/PrimitivePackets/" in row["candidate"]["path"]:
                self.assertIn("unconfirmed",row["candidate"]["owner"])
                self.assertNotIn("Assigned V09",row["candidate"]["owner_basis"])
        self.assertEqual(self.result["summary"]["verified_witnesses"],0)

if __name__=="__main__":
    unittest.main()
