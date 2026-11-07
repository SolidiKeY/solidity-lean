"""Guarded regression: non-state Osaka/transition/unresolved records must not vanish or become execution passes."""
import importlib.util
import sys
import unittest
from pathlib import Path
S=Path(__file__).resolve().parents[4]/"scripts/h62/item3/g52-differential"
sys.path.insert(0,str(S));spec=importlib.util.spec_from_file_location("archive",S/"archive_census.py");m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Inventory(unittest.TestCase):
 def test_state_variants(self):
  rows=m.inspect_fixture("p","n",{"_info":{"fixture-format":"state_test"},"post":{"Osaka":[{},{}],"Cancun":[{}]}})
  self.assertEqual(sum(r["variants"] for r in rows if r["selection"]=="exact-osaka"),2)
  self.assertTrue(all(r["status"]=="inventory-only-not-executed" for r in rows))
 def test_non_state_and_transition(self):
  for fork,selection in [("Osaka","exact-osaka"),("PragueToOsakaAtTime15k","osaka-transition-or-related")]:
   row=m.inspect_fixture("p","n",{"_info":{"fixture-format":"blockchain_test"},"network":fork})[0]
   self.assertEqual(row["selection"],selection);self.assertEqual(row["variants"],1)
 def test_unknown_and_empty_post_retained(self):
  for fixture in [{},{"post":{}}]:
   row=m.inspect_fixture("p","n",fixture)[0];self.assertEqual(row["selection"],"unresolved");self.assertEqual(row["format"],"unrecognized")
 def test_transaction_forks_from_result(self):
  rows=m.inspect_fixture("p","n",{"_info":{"fixture-format":"transaction_test"},"result":{"Osaka":{},"Cancun":{}}})
  self.assertEqual([r["selection"] for r in rows],["exact-osaka","other-fork"])
 def test_shared_support_is_not_fixture_padding(self):
  row=m.inspect_allocation_group("p",{"testIds":["a","b"],"network":"Osaka","pre":{},"testCount":2})
  self.assertEqual(row["variants"],0);self.assertEqual(row["referenced_cases"],2);self.assertEqual(row["role"],"support-allocation-group")
  with self.assertRaises(ValueError):m.inspect_allocation_group("p",{"network":"Osaka"})
if __name__=="__main__":unittest.main()
