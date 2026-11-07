import copy
import sys
from pathlib import Path
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[4]/'scripts/h62/item4/generic-internalflow'))
import census,embedded,prefix
class Prefix(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.inventory=census.census(embedded.BASE)
  cls.mapping=embedded.parse(prefix.MAP.read_text(),regions=prefix.REGIONS,facet_definitions=prefix.FACETS)
  cls.result=prefix.classify(cls.inventory,cls.mapping)
 def test_conservation(self):
  self.assertEqual(self.result['summary'],dict(regions=3,theorems=37,fixtures=17,unclassified_within_selected_regions=0))
  originals={f['path']:f for f in self.inventory['files']}
  for f in self.result['files']:
   before=[d for d in originals[f['path']]['declarations'] if f['begin']<d['line']<f['end']]
   self.assertEqual(len(before),len(f['declarations']))
   for x,y in zip(before,f['declarations']):
    for k,v in x.items():self.assertEqual(v,y[k])
 def test_omission_rejected(self):
  m=copy.deepcopy(self.mapping);del m['RuntimeFrameV3ParentPrefixes.lean']['horizons']
  with self.assertRaises(ValueError):prefix.classify(self.inventory,m)
 def test_distinctions(self):
  a=self.mapping['RuntimeFrameV3AllocatingPrefixes.lean'];m=self.mapping['RuntimeFrameV3MutatingPrefixes.lean']
  self.assertIn('heap_keeps',a['available']);self.assertIn('lengths',m['horizons']);self.assertNotIn('heap_keeps',m['horizons'])
  self.assertEqual(a['wrong_cost'],['growthneg'])
  self.assertTrue({'ss','ev','eq','ts'}<=set(m['available']))
  self.assertEqual(m['bad_horizons'],['loop','tr'])
  self.assertFalse(any('continuation' in tags for cases in self.mapping.values() for tags in cases.values()))
if __name__=='__main__':unittest.main()
