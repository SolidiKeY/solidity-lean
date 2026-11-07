import importlib.util,pathlib,unittest
p=pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item4/generic-v08/drift.py'
import sys
sys.path.insert(0,str(p.parent))
s=importlib.util.spec_from_file_location('drift',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
def row(name,sha,ordinal=1):return dict(path='X.lean',kind='theorem',name=name,statement_sha256=sha,ordinal=ordinal)
def inv(rows):return dict(declarations=rows,files=[])
class Drift(unittest.TestCase):
 def test_insert_does_not_repair_changed_statement(self):
  r=m.compare(inv([row('x','old')]),inv([row('new','n'),row('x','changed',2)]))
  self.assertEqual(r['counts'],{'added':1,'lexical-header-changed':1})
 def test_duplicate_names_not_zipped(self):
  r=m.compare(inv([row('x','a'),row('x','b',2)]),inv([row('x','a')]))
  self.assertEqual(r['counts'],{'ambiguous-no-pairing':1});self.assertEqual(r['accounted_before'],2)
 def test_removal_retained(self):
  r=m.compare(inv([row('x','a')]),inv([]));self.assertEqual(r['counts'],{'removed':1});self.assertEqual(r['accounted_after'],0)
class AnonymousDrift(unittest.TestCase):
 def test_insertion_never_pairs_example_ordinals(self):
  a={**row('@example:2','a',2),'kind':'example'}
  b={**row('@example:2','different',2),'kind':'example'}
  c={**row('@example:3','a',3),'kind':'example'}
  r=m.compare(inv([a]),inv([b,c]))
  self.assertEqual(r['counts'],{'anonymous-unpaired':1})
  self.assertEqual(r['accounted_before'],1);self.assertEqual(r['accounted_after'],2)
 def test_file_only_drift_stays_visible(self):
  a=inv([row('x','same')]);b=inv([row('x','same')])
  a['files']=[{'path':'X.lean','sha256':'old'}];b['files']=[{'path':'X.lean','sha256':'new'}]
  r=m.compare(a,b)
  self.assertNotEqual(r['before_files'],r['after_files'])
  self.assertIn('omit namespace',r['meaning'])
unittest.main()
