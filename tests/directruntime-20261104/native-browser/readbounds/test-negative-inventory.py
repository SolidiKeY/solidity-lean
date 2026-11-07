"""Guard independent negative expectations against same-wire status mutations.

Small synthetic wire fixtures exercise admission only; no native/browser replay.
The exact retained request journal pin is separately fixed in reviewed code.
"""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec=importlib.util.spec_from_file_location("inventory",Path(__file__).with_name("negative-inventory.py"))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class InventoryControls(unittest.TestCase):
    def fixtures(self):
        expected=copy.deepcopy(m.EXPECTED);requests=[]
        for index,row in enumerate(expected):
            wire=json.dumps({"fixture":index})
            row["wireSha256"]=hashlib.sha256(wire.encode()).hexdigest()
            requests.append(dict(copy.deepcopy(row),wire=wire))
        return expected,requests,copy.deepcopy(requests)

    def test_complete_inventory_and_false_assertion_outcomes(self):
        self.assertEqual(len(m.EXPECTED),7)
        self.assertEqual(sum(len(r["expected"]) for r in m.EXPECTED),14)
        final=dict(m.EXPECTED[-1]["expected"])
        for name in ("falseMaximum","falseConstant","falseStore"):
            self.assertEqual(final[name],["refuted"])
        expected,requests,records=self.fixtures()
        with patch.object(m,"EXPECTED",expected):self.assertEqual(m.validate(requests,records),requests)

    def test_false_maximum_mutation_preserves_wire_source_hashes_but_refuses(self):
        expected,requests,records=self.fixtures()
        original=(requests[-1]["wireSha256"],requests[-1]["sourceHash"])
        requests[-1]["expected"][1][1]=["proved"]
        records[-1]["expected"][1][1]=["proved"]
        self.assertEqual((requests[-1]["wireSha256"],requests[-1]["sourceHash"]),original)
        with patch.object(m,"EXPECTED",expected), self.assertRaisesRegex(ValueError,"inventory or expectations"):
            m.validate(requests,records)

    def test_missing_reordered_renamed_and_completion_mutations(self):
        for variant in ("missing","reordered","renamed","completion","wire","source"):
            expected,requests,records=self.fixtures()
            if variant=="missing":requests.pop()
            elif variant=="reordered":requests.reverse()
            elif variant=="renamed":requests[0]["expected"][0][0]="other"
            elif variant=="completion":records[-1]["expected"][1][1]=["proved"]
            elif variant=="wire":requests[0]["wire"]="different"
            else:requests[0]["sourceHash"]="0"*64
            with self.subTest(variant=variant),patch.object(m,"EXPECTED",expected),self.assertRaises(ValueError):
                m.validate(requests,records)

    def test_exact_journal_pin_rejects_mutated_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp)/"browser-control-attempts.jsonl").write_text("{}\n")
            with self.assertRaisesRegex(ValueError,"journal pin mismatch"):m.load(tmp)
        with self.assertRaisesRegex(ValueError,"duplicate replay"):m.pairs([("expected",1),("expected",2)])


if __name__=="__main__":unittest.main()
