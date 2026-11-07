"""Guard regression: duplicates, stale hashes or overlapping references fabricate coverage."""
import importlib.util
from pathlib import Path
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('classification_coverage', root / 'scripts/h55/module-times/classification_coverage.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class ClassificationCoverage(unittest.TestCase):
    def test_overlap_and_fail_closed(self):
        a = {'path':'a', 'sha256':'1'*64}
        b = {'path':'b', 'sha256':'2'*64}
        old = {'rows':[a]}
        delta = {'delta':{'added':[b], 'removed':[], 'changed_bytes':[], 'changed_mapping':[]}}
        artifact = {'rows':[{'candidate':a}]}
        rows = module.reconcile(old, delta, [('one',artifact), ('two',artifact)])
        self.assertEqual(['one','two'], rows[0]['static_reference_artifacts'])
        self.assertEqual('no-supplied-per-path-reference', rows[1]['status'])
        with self.assertRaises(ValueError):
            module.reconcile(old, delta, [('one',{'rows':[{'candidate':a},{'candidate':a}]})])
        with self.assertRaises(ValueError):
            module.reconcile(old, delta, [('one',{'rows':[{'candidate':{'path':'a','sha256':'stale'}}]})])
        with self.assertRaises(ValueError):
            module.reconcile({'rows':[{'path':'a'}]}, {'delta':{'added':[], 'removed':[], 'changed_bytes':[], 'changed_mapping':[]}}, [('one',{'rows':[{'candidate':{'path':'a'}}]})])
        with self.assertRaises(ValueError):
            module.reconcile({'rows':[{'path':'a','sha256':int('1'*64)}]}, {'delta':{'added':[], 'removed':[], 'changed_bytes':[], 'changed_mapping':[]}}, [])
        with self.assertRaises(ValueError):
            module.reconcile(old, {'delta':{**delta['delta'], 'changed_mapping':['a']}}, [])

if __name__ == '__main__':
    unittest.main()
