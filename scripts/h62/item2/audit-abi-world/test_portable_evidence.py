#!/usr/bin/env python3
"""Portable byte-integrity controls; no Lean, repo mutations or extraction."""
import hashlib,io,tarfile,tempfile,unittest
from pathlib import Path
from portable_evidence import verify
class PortableEvidenceTests(unittest.TestCase):
 def fixture(self,folder,name="proof/report.json",body=b"checked",expected=b"checked"):
  archive=folder/"evidence.tar.gz";manifest=folder/"evidence.sha256"
  with tarfile.open(archive,"w:gz") as tar:
   info=tarfile.TarInfo(name);info.size=len(body);tar.addfile(info,io.BytesIO(body))
  manifest.write_text(hashlib.sha256(expected).hexdigest()+"  "+name+"\n")
  return archive,manifest
 def test_valid_without_original_vm(self):
  with tempfile.TemporaryDirectory() as tmp:
   a,m=self.fixture(Path(tmp));self.assertEqual(verify(a,m),1)
 def test_changed_member_rejected(self):
  with tempfile.TemporaryDirectory() as tmp:
   a,m=self.fixture(Path(tmp),body=b"altered")
   with self.assertRaisesRegex(ValueError,"checksum mismatch"):verify(a,m)
 def test_escaping_path_rejected(self):
  with tempfile.TemporaryDirectory() as tmp:
   a,m=self.fixture(Path(tmp),name="../outside")
   with self.assertRaisesRegex(ValueError,"unsafe"):verify(a,m)
 def test_missing_member_rejected(self):
  with tempfile.TemporaryDirectory() as tmp:
   a,m=self.fixture(Path(tmp));m.write_text(m.read_text()+hashlib.sha256(b"x").hexdigest()+"  absent.json\n")
   with self.assertRaisesRegex(ValueError,"missing archive members"):verify(a,m)
if __name__=="__main__":unittest.main()
