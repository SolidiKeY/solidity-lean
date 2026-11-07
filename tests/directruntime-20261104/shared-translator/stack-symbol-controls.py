"""Guards historical symbol evidence against archive corruption and duplicate/gapped indices.
External integrity checks, not source/compiler or native correctness proofs.
"""
from pathlib import Path
import importlib.util,tempfile,unittest
from unittest.mock import patch
O=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('symbols',O/'verify-stack-symbols.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Controls(unittest.TestCase):
 def test_healthy(self):self.assertEqual(m.verify()['mappedFrameOccurrences'],10)
 def test_index_domain(self):
  self.assertEqual(m.symbol_table(b'0:a\n1:b\n',2),{0:'a',1:'b'})
  for raw in [b'0:a\n0:b\n',b'0:a\n2:b\n']:
   with self.assertRaisesRegex(AssertionError,'domain'):m.symbol_table(raw,2)
 def test_archive_tamper(self):
  with tempfile.TemporaryDirectory(dir=O/'artifacts') as tmp:
   p=Path(tmp)/'mutated.tar.gz';raw=m.ARCHIVE.read_bytes();p.write_bytes(b'!'+raw[1:])
   with patch.object(m,'ARCHIVE',p),self.assertRaises(AssertionError):m.verify()
if __name__=='__main__':unittest.main()
