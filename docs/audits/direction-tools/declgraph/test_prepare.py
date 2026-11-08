#!/usr/bin/env python3
"""Regression checks for Lake's distinct split-object content hashes."""
import pathlib,runpy,tempfile,unittest
HERE=pathlib.Path(__file__).resolve().parent
resolve=runpy.run_path(str(HERE/'prepare.py'))['recorded_artifacts']
class Artifacts(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.cache=pathlib.Path(self.tmp.name);(self.cache/'artifacts').mkdir()
 def put(self,*names):
  for name in names:(self.cache/'artifacts'/name).write_text(name)
 def test_split_uses_distinct_hashes(self):
  self.put('11.olean','22.olean.server','33.olean.private','44.ilean')
  files=resolve(self.cache,{'o':['11','22','33'],'i':'44'})
  self.assertEqual({k:v.name for k,v in files.items()},{'olean':'11.olean','olean.server':'22.olean.server','olean.private':'33.olean.private','ilean':'44.ilean'})
 def test_recorded_sidecar_missing_fails_even_with_main_hash_decoy(self):
  self.put('11.olean','11.olean.server','44.ilean')
  with self.assertRaisesRegex(FileNotFoundError,'22.olean.server'):resolve(self.cache,{'o':['11','22'],'i':'44'})
 def test_private_missing_fails(self):
  self.put('11.olean','22.olean.server','44.ilean')
  with self.assertRaisesRegex(FileNotFoundError,'33.olean.private'):resolve(self.cache,{'o':['11','22','33'],'i':'44'})
 def test_legacy_ignores_unrecorded_sidecar(self):
  self.put('11.olean','11.olean.server','44.ilean')
  self.assertEqual(set(resolve(self.cache,{'o':['11'],'i':'44'})),{'olean','ilean'})
 def test_invalid_hash_array_fails(self):
  for hs in ([],['1','2','3','4']):
   with self.assertRaises(ValueError):resolve(self.cache,{'o':hs,'i':'44'})
if __name__=='__main__':unittest.main()
