"""Guard regression: changed source inherits an old reference as current."""
import importlib.util
from pathlib import Path
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('reference_index_update', root/'scripts/h55/module-times/reference_index_update.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class ReferenceIndexUpdate(unittest.TestCase):
    def test_changed_and_new_sources(self):
        fields = {'category':'control','context':'standalone','module':None,'resolution':'review','collision':False}
        a = {'path':'a', 'sha256':'1'*64, **fields}
        b = {'path':'b', 'sha256':'2'*64, **fields}
        drift = {'rows':[{'candidate':a,'state':'changed-candidate-review','prior_reference_artifacts':['/old']},
                         {'candidate':b,'state':'new-candidate','prior_reference_artifacts':[]}]}
        rows = module.update(drift, [('/new',{'rows':[{'candidate':b}]})])
        self.assertEqual('no-supplied-current-reference', rows[0]['status'])
        self.assertEqual(['/old'], rows[0]['historical_references_require_review'])
        self.assertEqual(['/new'], rows[1]['current_static_references'])
        with self.assertRaises(ValueError):
            module.update(drift, [('/new',{'rows':[{'candidate':{**b,'sha256':'3'*64}}]})])
        with self.assertRaises(ValueError):
            module.update(drift, [('/new',{'rows':[{'candidate':{**b,'context':'stale'}}]})])
        with self.assertRaises(ValueError):
            module.update(drift, [('/new',{'rows':[{'candidate':{'path':'b','sha256':'2'*64}}]})])
        with self.assertRaises(ValueError):
            module.update(drift, [('/new',{'rows':[{'candidate':b},{'candidate':b}]})])
        with self.assertRaises(ValueError):
            module.update({'rows':[drift['rows'][0],drift['rows'][0]]}, [])

if __name__ == '__main__':
    unittest.main()
