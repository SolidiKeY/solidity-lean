#!/usr/bin/env python3
"""Adversarial post-merge receipt controls; no Lean or artifact mutations."""
import contextlib,hashlib,io,json,runpy,sys,unittest,os
from pathlib import Path
from unittest.mock import patch
folder=Path(__file__).resolve().parent
root=folder.parents[3]
e=Path(os.environ.get("H62_AUDIT_TEST_EVIDENCE","/workspace/audit-abi-world-evidence/resume-20261106"))
sys.path.insert(0,str(folder))
class ReceiptAuthorityTests(unittest.TestCase):
 def accept(self):
  with patch.object(sys,"argv",[str(folder/"resume_accept.py"),"--evidence",str(e)]),contextlib.redirect_stdout(io.StringIO()):
   runpy.run_path(str(folder/"resume_accept.py"),run_name="__main__")
 def test_current_complete_chain(self):self.accept()
 def test_replaced_archive_authority_rejected(self):
  original=Path.read_bytes;manifest=root/"tests/h62/item2/audit-abi-world/evidence.sha256"
  def read(path):
   data=original(path)
   return data+b"# forged replacement authority\n" if path==manifest else data
  with patch.object(Path,"read_bytes",read),self.assertRaisesRegex(AssertionError,"Archived manifest changed"):self.accept()
 def test_forged_upstream_with_rebound_output_rejected(self):
  report=e/"Fidelity.json";resource=e/"Fidelity-resource.json"
  changed=json.loads(report.read_text());changed["_audit"]["upstream_before"]["sha256"]="0"*64
  changed["_audit"]["upstream_after"]["sha256"]="0"*64
  body=json.dumps(changed).encode()
  guard=json.loads(resource.read_text());guard["stdout_sha256"]=hashlib.sha256(body).hexdigest()
  original_text=Path.read_text;original_bytes=Path.read_bytes
  def read_text(path,*args,**kwargs):
   if path==report:return body.decode()
   if path==resource:return json.dumps(guard)
   return original_text(path,*args,**kwargs)
  def read_bytes(path):return body if path==report else original_bytes(path)
  with patch.object(Path,"read_text",read_text),patch.object(Path,"read_bytes",read_bytes),self.assertRaisesRegex(AssertionError,"Upstream snapshot mismatch"):self.accept()
if __name__=="__main__":unittest.main()
