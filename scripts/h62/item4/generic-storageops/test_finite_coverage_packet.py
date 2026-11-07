#!/usr/bin/env python3
import subprocess,unittest
from pathlib import Path
import finite_coverage_packet as m
ROOT=Path(__file__).resolve().parents[4]
class PacketTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.old=subprocess.check_output(["git","show",m.BASE+":"+m.MODULE],cwd=ROOT)
    def test_exact_packet(self):
        current=(ROOT/m.MODULE).read_bytes();self.assertEqual(current,m.expected(self.old))
        report=m.verify(self.old,current)
        self.assertEqual(len(report["changed_proof_names"]),15)
        self.assertEqual(report["coverage_subproofs_replaced"],30)
    def test_tampering_rejected(self):
        source=m.expected(self.old)
        cases=[source.replace(b"theorem growing_bridge",b"theorem missing_case",1),
               source.replace(b"then w3 sourceOuter else",b"then w3 oldOuter else",1),
               source.replace(m.REPLACEMENT.encode(),b"  "+"· trivial\n".encode(),1),
               source.replace(b"i < outer",b"i <= outer",1),
               b"set_option maxHeartbeats 999999\n"+source,
               source.replace(b"\n",b"\r\n")]
        for candidate in cases:
            self.assertNotEqual(candidate,source)
            with self.subTest(candidate=candidate[:25]),self.assertRaises(ValueError):m.verify(self.old,candidate)
if __name__=="__main__":unittest.main()
