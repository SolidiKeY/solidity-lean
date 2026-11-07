import copy
import sys
from pathlib import Path
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[4]/"scripts/h62/item4/generic-internalflow"))
import census, embedded
class Embedded(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.inventory=census.census(embedded.BASE)
  cls.mapping=embedded.parse(embedded.MAP.read_text())
  cls.result=embedded.classify(cls.inventory,cls.mapping)
 def test_conservation(self):
  self.assertEqual(self.result['summary'],dict(regions=4,theorems=60,fixtures=26,unclassified_within_selected_regions=0))
  original={f['path']:f for f in self.inventory['files']}
  for f in self.result['files']:
   before=[d for d in original[f['path']]['declarations'] if f['begin']<d['line']<f['end']]
   self.assertEqual(len(before),len(f['declarations']))
   for x,y in zip(before,f['declarations']):
    for k,v in x.items():self.assertEqual(v,y[k])
 def test_missing_extra_duplicate_refused(self):
  for action in ('missing','extra'):
   m=copy.deepcopy(self.mapping);key='RuntimeFrameV3AllocatingSource.lean'
   if action=='missing':del m[key]['shallow']
   else:m[key]['invented']=['ss']
   with self.assertRaises(ValueError):embedded.classify(self.inventory,m)
  with self.assertRaises(ValueError):embedded.parse('@V3AllocatingSource\nss: x x')
 def test_continuation_and_preservation_distinction(self):
  a=self.mapping['RuntimeFrameV3AllocatingResume.lean']['available']
  m=self.mapping['RuntimeFrameV3MutatingResume.lean']['available']
  self.assertIn('continuation',a);self.assertIn('continuation',m)
  self.assertIn('heap_keeps',a);self.assertNotIn('heap_keeps',m);self.assertIn('lengths',m)
  self.assertEqual(self.mapping['RuntimeFrameV3AllocatingResume.lean']['still_needs_unwind'],['rneg'])
if __name__=='__main__':unittest.main()
