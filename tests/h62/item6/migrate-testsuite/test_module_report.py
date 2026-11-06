#!/usr/bin/env python3
"""Controls for partial-build reporting under the coordinator clarification."""
import copy,hashlib,importlib.util,json,tempfile,unittest
from pathlib import Path
root=Path(__file__).resolve().parents[4] if 'tests/h62' in str(Path(__file__).resolve()) else Path('/workspace/solidity-lean')
script=root/'scripts/h62/item6/migrate-testsuite/module-report.py'
if not script.exists(): script=Path(__file__).with_name('module-report.py')
spec=importlib.util.spec_from_file_location('module_report',script);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
class ModuleReportControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();p=Path(self.tmp.name);self.oldcfg=p/'old.toml';self.newcfg=p/'new.toml'
        self.oldcfg.write_text('buildDir = "old"\nenableArtifactCache = false\n');self.newcfg.write_text('buildDir = "new"\nenableArtifactCache = false\n')
        names=['D','M','Missing'];self.census={'module_paths':{n:n+'.lean' for n in names},'owned':{'M':{},'Missing':{}}}
        self.old={'results':[{'module':n,'exit':0,'stop':None,'wall_s':10,'sampled_aggregate_peak_rss_bytes':100,'command':['lake','-f',str(self.oldcfg)]} for n in names],'requested_modules':names,'source_hashes':{n+'.lean':'same' for n in names},'status':'pass','full_assigned_build':True,'settings':{'threads':1},'resources':{'memory.max':'fixed'},'parent_resources':{'memory.max':'fixed'},'runtime_image':'python@sha256:fixture','cpu_affinity':[0], 'versions':{'lean':'Lean (version 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b)','lake':'Lake (Lean version 4.24.0)'},'config_sha256':hashlib.sha256(self.oldcfg.read_bytes()).hexdigest()}
        self.new=copy.deepcopy(self.old);self.new['results']=self.new['results'][:2];self.new['status']='running';self.new['results'][1]['wall_s']=20
        for r in self.new['results']: r['command'][2]=str(self.newcfg)
        self.new['versions']={'lean':'Lean (version 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc)','lake':'Lake (Lean version 4.35.0)'};self.new['config_sha256']=hashlib.sha256(self.newcfg.read_bytes()).hexdigest()
    def tearDown(self): self.tmp.cleanup()
    def result(self): return module.report(self.old,self.new,self.census)
    def test_growth_reported_without_stop(self):
        r=self.result();self.assertEqual(r['rows'][1]['wall_delta_percent'],100);self.assertNotIn('status',r);self.assertEqual(r['new_status'],'running')
    def test_missing_module_not_comparable(self): self.assertFalse(self.result()['rows'][2]['comparable_successful_measurements'])
    def test_failed_record_not_comparable(self):
        self.new['results'][1]['exit']=1
        self.assertFalse(self.result()['rows'][1]['comparable_successful_measurements'])
    def test_changed_dependency_disables_comparison(self):
        self.new['source_hashes']['D.lean']='changed'
        self.assertFalse(self.result()['rows'][1]['comparable_successful_measurements'])
    def test_config_tampering_disables_comparison(self):
        self.newcfg.write_text('tampered')
        self.assertFalse(self.result()['rows'][1]['comparable_successful_measurements'])
    def test_wrong_version_disables_comparison(self):
        self.new['versions']=self.old['versions']
        self.assertFalse(self.result()['rows'][1]['comparable_successful_measurements'])
    def test_union_preserves_new_only_module(self):
        self.new['requested_modules'].append('New');self.new['source_hashes']['New.lean']='new';self.census['module_paths']['New']='New.lean'
        r=self.result();self.assertEqual(r['rows'][-1]['module'],'New');self.assertFalse(r['requested_modules_match'])
    def test_duplicate_request_rejected(self):
        self.new['requested_modules'].append('M')
        with self.assertRaisesRegex(ValueError,'DUPLICATE_REQUEST'): self.result()
    def test_unrequested_record_rejected(self):
        r=copy.deepcopy(self.new['results'][0]);r['module']='Unexpected';self.new['results'].append(r)
        with self.assertRaisesRegex(ValueError,'UNREQUESTED_MODULE_RECORD'): self.result()
    def test_unknown_census_module_rejected(self):
        del self.census['module_paths']['M']
        with self.assertRaisesRegex(ValueError,'MISSING_CENSUS_MODULE'): self.result()
    def test_nan_metric_rejected(self):
        self.new['results'][1]['wall_s']=float('nan')
        with self.assertRaisesRegex(ValueError,'INVALID_METRIC'): self.result()
if __name__=='__main__': unittest.main()
