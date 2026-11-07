"""Guards H68 intake rejection of semantic fixture drift, wrong pin counts and Lean edits.
External Python controls only; not Lean proofs or compiler replay.
"""
from pathlib import Path
import functools,importlib.util,json,unittest
from unittest.mock import patch
p=Path(__file__).with_name('verify-h68-intake.py')
spec=importlib.util.spec_from_file_location('h68_intake',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
original=functools.lru_cache(None)(m.blob)
class IntakeControls(unittest.TestCase):
 def check_mutation(self,mutate,marker):
  def changed(rev,path):return mutate(rev,path,original(rev,path))
  with patch.object(m,'blob',changed):
   with self.assertRaisesRegex(AssertionError,marker):m.verify()
 def test_healthy(self):
  with patch.object(m,'blob',original):self.assertEqual(m.verify()['fixtureCount'],34)
 def test_nonmetadata_fixture_change(self):
  def mutate(rev,path,raw):
   if rev==m.APPLY and path=='tests/solc/CallExceptions.ast.json':return raw+b' '
   return raw
  self.check_mutation(mutate,'fixture hash')
 def test_shared_pin_count_change(self):
  def mutate(rev,path,raw):
   if rev==m.APPLY and path=='tests/cr-canonical-reader/shared-translator-repins.json':
    d=json.loads(raw);d['pins'][0]['occurrences']+=1;return json.dumps(d).encode()
   return raw
  self.check_mutation(mutate,'')
 def test_corrected_census_semantic_change(self):
  def mutate(rev,path,raw):
   if rev==m.CORRECTED and path.endswith('/fixture-census.json'):
    d=json.loads(raw);d['counts']['knownKinds']+=1;return json.dumps(d).encode()
   return raw
  self.check_mutation(mutate,'not hash-only')
 def test_current_head_fixture_drift(self):
  def mutate(rev,path,raw):
   if rev==m.HEAD and path=='tests/solc/CallExceptions.ast.json':return raw+b' '
   return raw
  self.check_mutation(mutate,'current CR fixture drift')
 def test_duplicate_receipt_fixture(self):
  def mutate(rev,path,raw):
   if rev==m.APPLY and path.endswith('/h68-migration-applied.json'):
    d=json.loads(raw);rows=[r for r in d['fixtures'] if r.get('applied')];rows[1].update(rows[0]);return json.dumps(d).encode()
   return raw
  self.check_mutation(mutate,'')
if __name__=='__main__':unittest.main()
