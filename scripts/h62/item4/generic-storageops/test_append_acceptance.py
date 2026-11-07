#!/usr/bin/env python3
import subprocess, unittest
from pathlib import Path
import append_acceptance as a
class AcceptanceTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root=Path(subprocess.check_output(["git","rev-parse","--show-toplevel"],text=True).strip())
        cls.original=subprocess.check_output(["git","show",a.BASE+":"+a.MODULE],cwd=cls.root)
        cls.current=(cls.root/a.MODULE).read_bytes()
    def test_packet(self):self.assertTrue(a.verify(self.original,self.current)["existing_source_without_addition_identical"])
    def test_tampering(self):
        cases=[self.current.replace(b"import ",b"-- changed import ",1),
               self.current.replace(a.START.encode(),(a.START+a.START).encode(),1),
               self.current.replace(b"theorem modifyMany_append",b"theorem unexpected_append",1),
               self.current.replace(a.START.encode(),("set_option maxHeartbeats 999999\n"+a.START).encode(),1),
               self.current.replace(a.END.encode(),("axiom injected : False\n"+a.END).encode(),1),
               self.current.replace(b"\n",b"\r\n")]
        for source in cases:
            with self.subTest(source=source[:30]),self.assertRaises(ValueError):a.verify(self.original,source)
if __name__ == "__main__":unittest.main()
