"""Guard regression: stale context or duplicated artifact counts as new coverage."""
import importlib.util
from pathlib import Path
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('reference_index_extend', root/'scripts/h55/module-times/reference_index_extend.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class ReferenceIndexExtend(unittest.TestCase):
    def test_hash_context_and_historical_reference(self):
        candidate = {'path':'a', 'sha256':'1'*64, 'category':'control','context':'standalone',
                     'module':None,'resolution':'review','collision':False}
        index = {'rows':[{'candidate':candidate, 'current_static_references':[],
                          'historical_references_require_review':['/old'], 'status':'no-supplied-current-reference'}]}
        with self.assertRaises(ValueError):
            module.extend({**index, 'removed_from_candidate_set':[{'candidate':candidate}]}, [])
        with self.assertRaises(ValueError):
            module.extend({**index, 'removed_from_candidate_set':''}, [])
        with self.assertRaises(ValueError):
            module.extend({'rows':[{**index['rows'][0], 'historical_reference_records':[{'x':1}]}]}, [])
        rows = module.extend(index, [('/new', {'rows':[{'candidate':candidate}]})])
        self.assertEqual(['/old'], rows[0]['historical_references_require_review'])
        self.assertEqual(['/new'], rows[0]['current_static_references'])
        with self.assertRaises(ValueError):
            module.extend(index, [('/new', {'rows':[{'candidate':{**candidate,'context':'stale'}}]})])
        with self.assertRaises(ValueError):
            module.extend(index, [('/new', {'rows':[{'candidate':candidate},{'candidate':candidate}]})])
        with self.assertRaises(ValueError):
            module.extend(index, [('/new', {'rows':[{'candidate':{**candidate,'sha256':'2'*64}}]})])

if __name__ == '__main__':
    unittest.main()
