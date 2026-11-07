#!/usr/bin/env python3
"""Deterministic census and comparison negative controls; no Lean server."""
import copy, hashlib, importlib.util, json, subprocess, sys, tempfile, unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4] if 'tests/h62' in str(Path(__file__).resolve()) else Path('/workspace/solidity-lean')
SCRIPTS=ROOT/'scripts/h62/item6/migrate-testsuite'
sys.path.insert(0,str(SCRIPTS))
import census
spec=importlib.util.spec_from_file_location('comparison', SCRIPTS/'compare.py' if (SCRIPTS/'compare.py').exists() else Path(__file__).with_name('compare.py'))
comparison=importlib.util.module_from_spec(spec); spec.loader.exec_module(comparison)

collector_spec=importlib.util.spec_from_file_location('collector',SCRIPTS/'collect-interfaces.py')
collector=importlib.util.module_from_spec(collector_spec);collector_spec.loader.exec_module(collector)

class InterfaceControls(unittest.TestCase):
    def test_failed_compiler_refused(self):
        with self.assertRaisesRegex(ValueError,'INTERFACE_COMPILER_FAILED'): collector.collect({'owned':{'M':{}}},'',1)
    def test_empty_output_refused(self):
        with self.assertRaisesRegex(ValueError,'INCOMPLETE_INTERFACE_OUTPUT'): collector.collect({'owned':{'M':{}}},'',0)
    def test_missing_expression_roots_refused(self):
        log='H62-INTERFACE '+json.dumps({'name':'Solkey.TestSuite.additionStorageWrite.proved','module':'M','kind':'theorem'})
        with self.assertRaisesRegex(ValueError,'INVALID_INTERFACE_ROW'): collector.collect({'owned':{'M':{}}},log,0)
    def test_representatives_alone_not_full_case_inventory(self):
        def parts(name):
            value=['anonymous']
            for piece in name.split('.'): value=['str',value,piece]
            return value
        names=['Solkey.TestSuite.additionStorageWrite.proved','Solkey.TestSuite.storageRootReadWrite.proved','Solkey.TestSuite.additionStorageWrite.problem']
        rows=[{'name':n,'name_parts':parts(n),'module':'M','kind':'definition' if n.endswith('.problem') else 'theorem','level_params':[],'type_root':0,'value_root':0 if n.endswith('.problem') else None,'internal':False} for n in names]
        node={'module':'M','id':0,'tag':'const','data':[parts('True'),[]],'children':[]}
        log='H62-NODE '+json.dumps(node)+'\n'+'\n'.join('H62-INTERFACE '+json.dumps(r) for r in rows)+'\nH62-MODULE '+json.dumps({'module':'M','count':3,'nodes':1,'schema':'expr-dag-v2'})
        with self.assertRaisesRegex(ValueError,'FROZEN_CASE_COUNT_MISMATCH'): collector.collect({'owned':{'M':{}}},log,0)
    def test_zero_rows_refused(self):
        log='H62-MODULE '+json.dumps({'module':'M','count':0,'nodes':0,'schema':'expr-dag-v2'})
        with self.assertRaisesRegex(ValueError,'INCOMPLETE_INTERFACE_OUTPUT'): collector.collect({'owned':{'M':{}}},log,0)

class CensusControls(unittest.TestCase):
    def test_comment_string_and_dependency_controls(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/'Solidity/TestSuite').mkdir(parents=True)
            (root/'Solidity/Core.lean').write_text('def core : Nat := 1\n')
            owned=root/'Solidity/TestSuite/Case.lean'
            owned.write_text('/- import Wrong.Outer /- import Wrong.Inner -/ -/\nimport Solidity.Core\n-- import Wrong.Line\ndef text := "import Wrong.String"\nresume_memory_replay x\ntheorem original : True := True.intro\n')
            def git(*args): return subprocess.check_output(['git',*args],cwd=root,stderr=subprocess.DEVNULL,text=True)
            git('init','-q');git('add','.');git('-c','user.name=Control','-c','user.email=control@example.invalid','commit','-qm','fixture')
            oldbase=census.BASE
            try:
                census.BASE=git('rev-parse','HEAD').strip()
                s=census.scan(root)
                self.assertTrue(s['source_matches_pinned_base'])
                self.assertEqual(s['build_order'],['Solidity.Core','Solidity.TestSuite.Case'])
                self.assertEqual(s['owned']['Solidity.TestSuite.Case']['imports'],['Solidity.Core'])
                self.assertEqual(len(s['owned']['Solidity.TestSuite.Case']['commands']),1)
                before=s['owned']['Solidity.TestSuite.Case']['sha256']
                owned.write_text(owned.read_text().replace('original : True','original : False'))
                s=census.scan(root)
                self.assertFalse(s['source_matches_pinned_base'])
                self.assertNotEqual(before,s['owned']['Solidity.TestSuite.Case']['sha256'])
                (root/'Solidity/Core.lean').write_text('import Solidity.TestSuite.Case\n')
                with self.assertRaisesRegex(ValueError,'import cycle'): census.scan(root)
            finally: census.BASE=oldbase

class TimingControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); p=Path(self.tmp.name)
        self.oldcfg=p/'old.toml';self.newcfg=p/'new.toml'
        self.oldcfg.write_text('buildDir = "old"\nenableArtifactCache = false\n')
        self.newcfg.write_text('buildDir = "new"\nenableArtifactCache = false\n')
        self.old={'status':'pass','full_assigned_build':True,'requested_modules':['X'],'source_hashes':{'X':'hash'},'settings':{'threads':1},'resources':{'cpu.max':'fixed'},'parent_resources':{'memory.max':'fixed'},'runtime_image':'python@sha256:fixture','cpu_affinity':[0],'wall_s':100,'results':[{'module':'X','exit':0,'stop':None,'sampled_aggregate_peak_rss_bytes':100,'command':['lake','-f',str(self.oldcfg)]}]}
        self.old['config_sha256']=hashlib.sha256(self.oldcfg.read_bytes()).hexdigest()
        self.old['versions']={'lean':'Lean (version 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b)','lake':'Lake (Lean version 4.24.0)'}
        self.new=copy.deepcopy(self.old)
        self.new['config_sha256']=hashlib.sha256(self.newcfg.read_bytes()).hexdigest()
        self.new['versions']={'lean':'Lean (version 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc)','lake':'Lake (Lean version 4.35.0)'}
        self.new['results'][0]['command'][2]=str(self.newcfg)
    def tearDown(self): self.tmp.cleanup()
    def test_private_paths_normalized(self): self.assertEqual(comparison.compare(self.old,self.new)['status'],'pass')
    def test_partial_refused(self):
        self.new['full_assigned_build']=False
        self.assertEqual(comparison.compare(self.old,self.new)['blocker'],'INCOMPLETE_FULL_BUILD')
    def test_source_change_refused(self):
        self.new['source_hashes']['X']='changed'
        self.assertEqual(comparison.compare(self.old,self.new)['blocker'],'UNMATCHED_MEASUREMENT')
    def test_config_change_refused(self):
        self.newcfg.write_text('buildDir = "new"\nenableArtifactCache = true\n')
        self.new['config_sha256']=hashlib.sha256(self.newcfg.read_bytes()).hexdigest()
        self.assertEqual(comparison.compare(self.old,self.new)['blocker'],'UNMATCHED_CONFIG')
    def test_small_regression_escalates(self):
        self.new['wall_s']=101
        self.assertEqual(comparison.compare(self.old,self.new)['status'],'escalate')
    def test_large_regression_stops(self):
        self.new['wall_s']=111
        self.assertEqual(comparison.compare(self.old,self.new)['status'],'stop')
    def test_rss_regression_stops(self):
        self.new['results'][0]['sampled_aggregate_peak_rss_bytes']=111
        self.assertEqual(comparison.compare(self.old,self.new)['status'],'stop')
    def test_exact_ten_escalates(self):
        self.new['wall_s']=110
        self.assertEqual(comparison.compare(self.old,self.new)['status'],'escalate')
    def test_nan_refused(self):
        self.new['wall_s']=float('nan')
        self.assertEqual(comparison.compare(self.old,self.new)['blocker'],'INVALID_METRIC')
    def test_zero_refused(self):
        self.new['wall_s']=0
        self.assertEqual(comparison.compare(self.old,self.new)['blocker'],'INVALID_METRIC')
    def test_nan_rss_refused(self):
        self.new['results'][0]['sampled_aggregate_peak_rss_bytes']=float('nan')
        self.assertEqual(comparison.compare(self.old,self.new)['blocker'],'INVALID_METRIC')
    def test_config_digest_refused(self):
        self.newcfg.write_text('tampered')
        self.assertEqual(comparison.compare(self.old,self.new)['blocker'],'CONFIG_DIGEST_MISMATCH')
    def test_wrong_version_refused(self):
        self.new['versions']=self.old['versions']
        self.assertEqual(comparison.compare(self.old,self.new)['blocker'],'UNEXPECTED_TOOLCHAIN')
    def test_runtime_change_refused(self):
        self.new['runtime_image']='python@sha256:different'
        self.assertEqual(comparison.compare(self.old,self.new)['field'],'runtime_image')
    def test_parent_change_refused(self):
        self.new['parent_resources']['memory.max']='different'
        self.assertEqual(comparison.compare(self.old,self.new)['field'],'parent_resources')
    def test_failed_record_refused(self):
        self.new['results'][0]['exit']=1
        self.assertEqual(comparison.compare(self.old,self.new)['blocker'],'INCONSISTENT_BUILD_RECORDS')
if __name__=='__main__': unittest.main()
