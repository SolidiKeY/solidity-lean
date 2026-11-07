"""Guard regression: changed or removed candidates lose historic reference identity."""
import importlib.util
from pathlib import Path
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('rebase_reference_index', root/'scripts/h55/module-times/rebase_reference_index.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class RebaseReferenceIndex(unittest.TestCase):
    def test_changed_and_removed_are_preserved(self):
        c = {'path':'a','sha256':'1'*64,'category':'control','context':'standalone','module':None,'resolution':'review','collision':False}
        old = {'rows':[{'candidate':c,'current_static_references':['/one'],'historical_references_require_review':['/older'],'status':'referenced-static-only'}]}
        d = {'candidate':{**c,'sha256':'2'*64},'state':'changed-candidate-review','prior_reference_artifacts':['/one'],
             'historical_references_require_review':['/older','/one'],'changed_bytes':True,'changed_mapping':False}
        rows, removed = module.rebase(old, {'rows':[d], 'removed_from_candidate_set':[]})
        self.assertEqual([], rows[0]['current_static_references'])
        self.assertEqual(c, rows[0]['historical_reference_records'][0]['candidate_at_reference'])
        next_drift = {'candidate':d['candidate'],'state':'no-supplied-per-path-reference','prior_reference_artifacts':[],
                      'historical_references_require_review':['/older','/one'],'changed_bytes':False,'changed_mapping':False}
        again, _ = module.rebase({'rows':rows}, {'rows':[next_drift], 'removed_from_candidate_set':[]})
        self.assertEqual(rows[0]['historical_reference_records'], again[0]['historical_reference_records'])
        removed_again = {'candidate':d['candidate'],'static_reference_artifacts':[],
                         'historical_references_require_review':['/older','/one']}
        self.assertEqual(rows, module.rebase({'rows':rows}, {'rows':[], 'removed_from_candidate_set':[removed_again]})[1])
        self.assertEqual([], removed)
        gone = {'candidate':c,'static_reference_artifacts':['/one'],'historical_references_require_review':['/older']}
        self.assertEqual(old['rows'], module.rebase(old, {'rows':[], 'removed_from_candidate_set':[gone]})[1])
        self.assertEqual(old['rows'], module.rebase({'rows':[], 'removed_from_candidate_set':old['rows']}, {'rows':[], 'removed_from_candidate_set':[]})[1])
        with self.assertRaises(ValueError):
            module.rebase({'rows':[], 'removed_from_candidate_set':old['rows']}, {'rows':[d], 'removed_from_candidate_set':[]})
        with self.assertRaises(ValueError):
            module.rebase({'rows':[], 'removed_from_candidate_set':''}, {'rows':[], 'removed_from_candidate_set':[]})
        with self.assertRaises(ValueError):
            module.rebase(old, {'rows':[{**d,'historical_references_require_review':['/older']}], 'removed_from_candidate_set':[]})
        with self.assertRaises(ValueError):
            module.rebase(old, {'rows':[], 'removed_from_candidate_set':[]})
        with self.assertRaises(ValueError):
            module.rebase(old, {'rows':[{**d,'changed_bytes':False}], 'removed_from_candidate_set':[]})
        mapping = {**d, 'candidate':{**c,'context':'new'}, 'changed_bytes':False, 'changed_mapping':True}
        self.assertEqual('no-supplied-current-reference', module.rebase(old, {'rows':[mapping], 'removed_from_candidate_set':[]})[0][0]['status'])
        fresh = {'candidate':{**c,'path':'b'}, 'state':'new-candidate', 'prior_reference_artifacts':[],
                 'historical_references_require_review':[], 'changed_bytes':False, 'changed_mapping':False}
        rows, _ = module.rebase(old, {'rows':[d,fresh], 'removed_from_candidate_set':[]})
        self.assertEqual(2, len(rows))
        with self.assertRaises(ValueError):
            module.rebase(old, {'rows':[d,{**fresh,'prior_reference_artifacts':['/forged']}], 'removed_from_candidate_set':[]})

if __name__ == '__main__':
    unittest.main()
