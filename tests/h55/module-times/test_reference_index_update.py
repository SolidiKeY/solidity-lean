"""Guard regression: changed source inherits an old reference as current."""
import importlib.util
from pathlib import Path
import unittest
import sys
import hashlib
import json
import tempfile
import subprocess

root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root/'scripts/h55/module-times'))
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


    def test_extended_versions_and_removed_rows(self):
        fields = {'category':'control','context':'standalone','module':None,'resolution':'review','collision':False}
        c = {'path':'a','sha256':'1'*64,**fields}
        old = {'rows':[{'candidate':c,'current_static_references':['/one'],
                        'historical_references_require_review':['/older'],'status':'referenced-static-only'}]}
        changed = {'candidate':{**c,'sha256':'2'*64},'state':'changed-candidate-review',
                   'prior_reference_artifacts':['/one'],'historical_references_require_review':['/older','/one'],
                   'changed_bytes':True,'changed_mapping':False}
        drift = {'rows':[changed],'removed_from_candidate_set':[]}
        rows, removed = module.update_extended(old,drift,[],{'/one':'a'*64},{'/one':'a'*64})
        self.assertEqual([],removed)
        self.assertEqual([],rows[0]['current_static_references'])
        record = rows[0]['historical_reference_records'][0]
        self.assertEqual(c,record['candidate_at_reference'])
        self.assertEqual(['/older'],rows[0]['unbound_historical_reference_artifacts'])
        self.assertEqual([{'path':'/one','sha256':'a'*64}],record['artifact_versions'])
        with self.assertRaises(ValueError):
            module.update_extended(old,drift,[],{'/one':'b'*64},{'/one':'a'*64})
        gone = {'candidate':c,'static_reference_artifacts':['/one'],'historical_references_require_review':['/older']}
        rows, tombstones = module.update_extended(old,{'rows':[],'removed_from_candidate_set':[gone]},[],{'/one':'a'*64},{'/one':'a'*64})
        self.assertEqual([],rows)
        self.assertEqual([{'path':'/one','sha256':'a'*64}],tombstones[0]['tombstone_reference_versions'])
        self.assertNotIn('tombstone_reference_versions', old['rows'][0])
        historical = {'candidate_at_reference':{**c,'sha256':'0'*64}, 'artifact_paths':['/older'], 'status':'historical-reference-needs-review'}
        old_with_history = {'rows':[{**old['rows'][0], 'historical_reference_records':[historical]}]}
        _, tombstones = module.update_extended(old_with_history,{'rows':[],'removed_from_candidate_set':[gone]},[],
                                                {'/one':'a'*64,'/older':'b'*64},{'/one':'a'*64,'/older':'b'*64})
        self.assertEqual([{'path':'/older','sha256':'b'*64}],tombstones[0]['historical_reference_records'][0]['artifact_versions'])
        self.assertEqual([],tombstones[0]['unbound_historical_reference_artifacts'])
        with self.assertRaises(ValueError):
            module.update_extended(old_with_history,{'rows':[],'removed_from_candidate_set':[gone]},[],
                                   {'/one':'a'*64,'/older':'c'*64},{'/one':'a'*64,'/older':'b'*64})
        with self.assertRaises(ValueError):
            module.update_extended(old,{'rows':[],'removed_from_candidate_set':[gone]},[],{'/one':'b'*64},{'/one':'a'*64})
        with self.assertRaises(ValueError):
            module.update({'rows':[changed],'removed_from_candidate_set':[]},[])

    def test_version_lineage_rejects_overwritten_artifact(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)/'artifact.json'
            p.write_text('{}')
            sha = hashlib.sha256(p.read_bytes()).hexdigest()
            index = {'inputs':[{'path':str(p),'sha256':sha}]}
            self.assertEqual(sha,module.lineage_versions(index)[str(p)])
            p.write_text('{"changed":true}')
            with self.assertRaises(ValueError):
                module.lineage_versions(index)
            with self.assertRaises(ValueError):
                module.parse_versions((sha+'  '+str(p)+'\n').encode())


    def test_extended_cli_historical_delta_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            fields = {'category':'control', 'context':'standalone', 'module':None,
                      'resolution':'review', 'collision':False}
            candidate = {'path':'a', 'sha256':'1'*64, **fields}
            def write(name, value):
                p = base/name
                p.write_text(json.dumps(value))
                return p
            def sha(path):
                return hashlib.sha256(path.read_bytes()).hexdigest()
            delta = write('delta.json', {'delta':{'added':[], 'removed':[],
                'changed_bytes':[], 'changed_mapping':[]}})
            baseline = write('index.json', {'inputs':[{'path':str(delta), 'sha256':sha(delta)}],
                'rows':[{'candidate':candidate, 'current_static_references':[],
                         'historical_references_require_review':[], 'status':'no-supplied-current-reference'}]})
            drift = write('drift.json', {'head':'synthetic', 'input_sha256':sha(baseline),
                'rows':[{'candidate':candidate, 'state':'no-supplied-per-path-reference',
                         'prior_reference_artifacts':[], 'historical_references_require_review':[],
                         'changed_bytes':False, 'changed_mapping':False}], 'removed_from_candidate_set':[]})
            versions = base/'versions'; versions.write_text('')
            classification = write('class.json', {'input_sha256':sha(delta), 'rows':[{'candidate':candidate}]})
            command = [sys.executable, str(root/'scripts/h55/module-times/reference_index_update.py'),
                       str(drift), str(baseline), str(versions), '--delta', str(delta), str(classification)]
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(0, result.returncode, result.stderr)
            output = json.loads(result.stdout)
            self.assertEqual(1, output['referenced'])
            self.assertIn({'path':str(delta), 'sha256':sha(delta)}, output['inputs'])
            stale = write('stale.json', {'input_sha256':sha(delta), 'rows':[{'candidate':{**candidate, 'sha256':'2'*64}}]})
            self.assertNotEqual(0, subprocess.run(command[:-1]+[str(stale)], capture_output=True).returncode)
            other = write('other.json', {'delta':{'added':[], 'removed':[], 'changed_bytes':[], 'changed_mapping':[]}})
            self.assertNotEqual(0, subprocess.run(command[:-2]+[str(other), str(classification)], capture_output=True).returncode)
            delta.write_text('{"delta": {}}')
            self.assertNotEqual(0, subprocess.run(command, capture_output=True).returncode)

if __name__ == '__main__':
    unittest.main()
