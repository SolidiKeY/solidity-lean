#!/usr/bin/env python3
"""Launcher-only tests. No Lean, Docker, proof, EVM or package operation."""
import importlib.util,json,os,subprocess,sys,tempfile,unittest
from pathlib import Path
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('shim',root/'scripts/roadmap-v15-serial-shim.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Tests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory(prefix='v15-shim-test-');self.addCleanup(self.tmp.cleanup)
  self.base=Path(self.tmp.name);self.real=self.base/'real';(self.real/'bin').mkdir(parents=True);(self.real/'lib').mkdir()
  fake='#!'+sys.executable+'\nimport os,sys,json\nprint(json.dumps({"argv":sys.argv[1:],"override":os.getenv("LAKE_OVERRIDE_LEAN"),"threads":os.getenv("LEAN_NUM_THREADS"),"sysroot":os.getenv("LEAN_SYSROOT"),"lean":os.getenv("LEAN")}))\n'
  for name in ['lean','lake']:
   p=self.real/'bin'/name;p.write_text(fake);p.chmod(0o755)
  self.shim=self.base/'shim';m.install(self.real,self.shim,self.base/'configs',self.base/'overrides.json')
 def call(self,kind,*args):
  return subprocess.run([str(self.shim/'bin'/kind),*args],cwd=root,env={**os.environ,'LEAN_NUM_THREADS':'8'},capture_output=True,text=True)
 def test_injects_one_thread_preserves_literal_arguments(self):
  q=self.call('lean','path with spaces; $(literal).lean');self.assertEqual(q.returncode,0)
  data=json.loads(q.stdout);self.assertEqual(data['argv'],['-j1','path with spaces; $(literal).lean']);self.assertEqual(data['threads'],'1')
 def test_normalizes_redundant_serial_options(self):
  data=json.loads(self.call('lean','-j1','-j','1','--version').stdout);self.assertEqual(data['argv'],['-j1','--version'])
 def test_rejects_parallel_override(self):
  for args in [('-j2',),('-j','2')]:self.assertEqual(self.call('lean',*args).returncode,2)
 def test_lake_env_and_native_cli(self):
  q=self.call('lake','-j1','env','lean','--version');self.assertEqual(q.returncode,0)
  data=json.loads(q.stdout);self.assertEqual(data['override'],'true');self.assertEqual(data['threads'],'1');self.assertEqual(data['sysroot'],str(self.shim));self.assertEqual(data['lean'],str(self.shim/'bin/lean'));self.assertNotIn('-j1',data['argv']);self.assertEqual(data['argv'][-3:],['env','lean','--version'])
 def test_lake_preserves_nested_lean_serial_flag(self):
  data=json.loads(self.call('lake','-j1','env','lean','-j1','--version').stdout)
  self.assertEqual(data['argv'][-4:],['env','lean','-j1','--version'])
 def test_dangling_frontend_symlink_is_preserved(self):
  target=self.shim/'bin/lean';target.unlink();outside=self.base/'missing-outside';target.symlink_to(outside)
  with self.assertRaises(AssertionError):m.install(self.real,self.shim,self.base/'configs',self.base/'overrides.json')
  self.assertTrue(target.is_symlink());self.assertFalse(outside.exists())
 def test_symlinked_bin_is_rejected(self):
  other=self.base/'other';other.mkdir();view=self.base/'view';view.mkdir();(view/'bin').symlink_to(other,target_is_directory=True)
  with self.assertRaises(AssertionError):m.install(self.real,view,self.base/'configs',self.base/'overrides.json')
  self.assertEqual(list(other.iterdir()),[])
 def test_library_identity_and_non_destructive_install(self):
  self.assertTrue((self.shim/'lib').is_symlink());self.assertEqual((self.shim/'lib').resolve(),self.real/'lib')
  old=(self.shim/'bin/lean').read_bytes();m.install(self.real,self.shim,self.base/'configs',self.base/'overrides.json');self.assertEqual(old,(self.shim/'bin/lean').read_bytes())
  (self.shim/'bin/lean').write_text('unexpected')
  with self.assertRaises(AssertionError):m.install(self.real,self.shim,self.base/'configs',self.base/'overrides.json')
  self.assertEqual((self.shim/'bin/lean').read_text(),'unexpected')
if __name__=='__main__':unittest.main(verbosity=2)
