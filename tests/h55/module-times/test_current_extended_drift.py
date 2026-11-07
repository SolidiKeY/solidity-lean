"""Guard regression: extending a reference index drops stale or historical evidence."""
import importlib.util
from pathlib import Path
import sys
import unittest

root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root/'scripts/h55/module-times'))
spec = importlib.util.spec_from_file_location('current_extended_drift', root/'scripts/h55/module-times/current_extended_drift.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class CurrentExtendedDrift(unittest.TestCase):
    def test_changed_and_removed_preserve_history(self):
        row = {'path':'a','sha256':'1'*64,'context':'old'}
        index = {'rows':[{'candidate':row,'current_static_references':['/current'],
                          'historical_references_require_review':['/older'],'status':'referenced-static-only'}]}
        rows, removed = module.reconcile(index,[{**row,'sha256':'2'*64}])
        self.assertEqual('changed-candidate-review',rows[0]['state'])
        self.assertEqual(['/current'],rows[0]['prior_reference_artifacts'])
        self.assertEqual(['/current','/older'],rows[0]['historical_references_require_review'])
        self.assertEqual(['/older'],module.reconcile(index,[])[1][0]['historical_references_require_review'])
        with self.assertRaises(ValueError):
            module.reconcile({'rows':[{**index['rows'][0], 'historical_references_require_review':['/x/../bad']}]}, [])
        with self.assertRaises(ValueError):
            module.reconcile({'rows':[{**index['rows'][0], 'status':'no-supplied-current-reference'}]}, [])

if __name__ == '__main__':
    unittest.main()
