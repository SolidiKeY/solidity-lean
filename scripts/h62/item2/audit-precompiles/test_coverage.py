#!/usr/bin/env python3
"""Mutation checks for stale/failed partial proof receipts, without source writes."""
import json, os, pathlib, shutil, subprocess, sys, tempfile, unittest
HERE=pathlib.Path(__file__).resolve().parent
EVIDENCE=pathlib.Path(os.environ.get('H62_AUDIT_EVIDENCE','/workspace/h62-audit-precompiles-evidence-2'))
class CoverageTests(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory(prefix='h62-coverage-',dir=str(EVIDENCE))
  self.dir=pathlib.Path(self.temp.name)
  for stem in ['basic-final','core-final','data-final']:
   for suffix in ['.json','.log']: shutil.copyfile(EVIDENCE/(stem+suffix),self.dir/(stem+suffix))
 def tearDown(self): self.temp.cleanup()
 def run_check(self):
  return subprocess.run([sys.executable,str(HERE/'coverage.py'),'--evidence',str(self.dir)],capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')).returncode
 def edit(self,fn):
  p=self.dir/'basic-final.json';x=json.loads(p.read_text());fn(x);p.write_text(json.dumps(x))
 def test_valid_partial_receipts(self): self.assertEqual(self.run_check(),0)
 def test_failed_receipt_rejected(self):
  self.edit(lambda x:x.update(exit=1));self.assertNotEqual(self.run_check(),0)
 def test_wrong_working_directory_rejected(self):
  self.edit(lambda x:x.update(cwd='/wrong'));self.assertNotEqual(self.run_check(),0)
 def test_stale_import_hash_rejected(self):
  def change(x):
   key=next(k for k in x['input_sha256'] if k.endswith('/Solidity/Hashes.lean'))
   x['input_sha256'][key]='0'*64
  self.edit(change);self.assertNotEqual(self.run_check(),0)
 def test_failed_axiom_log_rejected(self):
  p=self.dir/'basic-final.log';p.write_text(p.read_text()+'\nsorryAx\n');self.assertNotEqual(self.run_check(),0)
 def test_missing_data_witness_receipt_rejected(self):
  (self.dir/'data-final.json').unlink();self.assertNotEqual(self.run_check(),0)
if __name__=='__main__': unittest.main()
