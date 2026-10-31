"""Synthetic provenance controls; no kernel proof or actual clean build claimed."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import shlex
import subprocess
from types import SimpleNamespace
from unittest.mock import patch, MagicMock
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('provenance', ROOT/'scripts/roadmap-v17-provenance.py')
p = importlib.util.module_from_spec(spec); spec.loader.exec_module(p)
e = p.e


class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        marker=patch.object(p,'UNRESOLVED',self.root/'unresolved.json'); marker.start(); self.addCleanup(marker.stop)
        self.current = {'schema':1,'revision':'1'*40,'sourceTree':'2'*40,
                        'sourceToolchainKey':'a'*64, 'serialConfigSha256':e.digest(b'config'),
                        'repository':str(self.root),'inputs':{'lakefile.toml':'b'*64},
                        'runtime':{name:{'path':'/usr/bin/'+name,'sha256':c*64,'version':name+' version'} for name,c in [('lean','c'),('lake','d')]}}
        self.current['buildTools'] = {name: {'path':'/usr/bin/'+name,'sha256':'c'*64 if name=='lean' else 'e'*64} for name in e.BUILD_TOOL_NAMES}
        self.build = self.root/'.lake/build'; self.build.mkdir(parents=True)
        self.cache = self.root/'.lake/roadmap-v17-cache'/('a'*64); self.cache.mkdir(parents=True)
        path=self.build/'lib/lean/Solidity/Evm/Compiler.olean'; path.parent.mkdir(parents=True); path.write_bytes(b'artifact')
        (self.cache/'token').write_bytes(b'cached')
        self.clean=self.record('clean'); self.warm=self.record('warm')

    def attach(self, name, data):
        (self.root/name).write_bytes(data); return e.digest(data)

    def record(self, mode):
        name=mode+'-compiler'
        runtime={'entrypointHashes':{tool:e.digest(p.launcher_bytes(tool)) for tool in e.BUILD_TOOL_NAMES},'toolHashes':{k:v['sha256'] for k,v in self.current['buildTools'].items()},'memoryMax':p.CAP,'swapMax':0,'memoryPeak':1024,'image':p.IMAGE,
                 'realLeanSha256':'c'*64,'lakeSha256':'d'*64,'leanVersion':'lean version','lakeVersion':'lake version','leanNumThreads':'1'}
        r={'schema':2,'buildTools':copy.deepcopy(self.current['buildTools']),'collectionDirectory':str(self.root),'gate':name,'mode':mode,'before':copy.deepcopy(self.current),'after':copy.deepcopy(self.current),
           'budgets':copy.deepcopy(p.BUDGET),'configuration':mode+'.toml','configurationSha256':self.attach(mode+'.toml',b'config'),
           'configurationAfterSha256':e.digest(b'config'),
           'launcher':'lean-launcher','launcherSha256':self.attach('lean-launcher',p.launcher_bytes()),
           'runtime':mode+'.runtime','runtimeSha256':self.attach(mode+'.runtime',json.dumps(runtime).encode()),
           'samples':mode+'.samples','samplesSha256':self.attach(mode+'.samples',b'[{"rssBytes":10,"leanWorkers":1}]'),
           'log':mode+'.log','logSha256':self.attach(mode+'.log',b'Build completed successfully\n'),
           'exit':0,'headroomBytes':3*1024**3,'diskFreeBytes':2*1024**3,'elapsedSeconds':1,
           'command':['lake','-f','roadmap-v17-runtime.lakefile.toml','build','Solidity.Evm.Compiler'],
           'buildStart':p.inventory(self.build),'cacheStart':p.inventory(self.cache),
           'buildEnd':p.inventory(self.build),'cacheEnd':p.inventory(self.cache)}
        r['serializers']={}
        for tool in e.BUILD_TOOL_NAMES:
            path=tool+'-launcher'
            r['serializers'][tool]={'path':path,'sha256':self.attach(path,p.launcher_bytes(tool))}
        r['containerName']='roadmap-v17-'+'a'*32
        r['dockerArgv']=mode+'.docker.json'
        r['dockerArgvSha256']=self.attach(r['dockerArgv'],json.dumps(p.docker_create_argv(self.root,self.current,r['containerName'],r['command'])).encode())
        r['executionScript']=mode+'.sh'
        r['executionScriptSha256']=self.attach(mode+'.sh',p.execution_script(self.root,r['command'],Path(self.current['runtime']['lake']['path'])).encode())
        if mode=='clean':
            r['buildStart']['files']={}; r['cacheStart']['files']={}
        return r

    def validate(self, record=None):
        r=self.clean if record is None else record
        return p.validate(r,self.root,self.current,r['gate'])

    def pair(self):
        runs={}
        for mode,r in [('clean',self.clean),('warm',self.warm)]:
            path=mode+'.json'; runs[mode]={'path':path,'sha256':self.attach(path,json.dumps(r).encode())}
        return p.validate_pair({'runs':runs},self.root,self.current)

    def test_inhabited_clean_warm_pair(self):
        self.assertTrue(self.pair()['accountingComplete'])
        self.assertFalse(self.pair()['releaseClosed'])

    def test_warm_labeled_clean(self):
        self.clean['buildStart']=copy.deepcopy(self.clean['buildEnd'])
        with self.assertRaisesRegex(ValueError,'clean starting'): self.validate()

    def test_nonempty_clean_cache(self):
        self.clean['cacheStart']=copy.deepcopy(self.clean['cacheEnd'])
        with self.assertRaisesRegex(ValueError,'clean starting'): self.validate()

    def test_missing_provenance_rejected_by_aggregate(self):
        row={'id':'clean-compiler','revision':'1'*40,'command':['lake','build','Solidity.Evm.Compiler'],
             'exit':0,'status':'pass','log':'clean.log','sha256':self.clean['logSha256']}
        report={'schema':1,'revision':'1'*40,'gates':[row]}
        with self.assertRaisesRegex(ValueError,'missing build provenance'):
            e.aggregate(report,self.root,'1'*40,['clean-compiler'],self.current)

    def test_aggregate_validates_provenance_bytes_and_log_binding(self):
        raw=json.dumps(self.clean).encode(); sha=self.attach('proof.json',raw)
        row={'id':'clean-compiler','revision':'1'*40,'command':self.clean['command'],
             'exit':0,'status':'pass','log':'clean.log','sha256':self.clean['logSha256'],
             'provenance':'proof.json','provenanceSha256':sha}
        report={'schema':1,'revision':'1'*40,'gates':[row]}
        self.assertTrue(e.aggregate(report,self.root,'1'*40,['clean-compiler'],self.current)['accountingComplete'])
        self.attach('proof.json',raw+b'corruption')
        with self.assertRaisesRegex(ValueError,'corrupt'): e.aggregate(report,self.root,'1'*40,['clean-compiler'],self.current)

    def test_source_tree_toolchain_inputs_and_key_change(self):
        for field in ['revision','sourceTree','sourceToolchainKey','runtime','inputs']:
            bad=copy.deepcopy(self.clean); bad['after'][field]='changed'
            with self.assertRaisesRegex(ValueError,'source/toolchain'): self.validate(bad)

    def test_configuration_and_budget_change(self):
        for field in ['configurationSha256','configurationAfterSha256','budgets']:
            bad=copy.deepcopy(self.clean); bad[field]='changed'
            with self.assertRaises(ValueError): self.validate(bad)

    def test_cache_identity(self):
        self.clean['cacheStart']['path']=str(self.root/'wrong-key')
        with self.assertRaisesRegex(ValueError,'cache location'): self.validate()

    def test_unrelated_build_or_cache_parent(self):
        for field in ['buildStart','buildEnd','cacheStart','cacheEnd']:
            bad=copy.deepcopy(self.clean)
            bad[field]['path']=str(self.root/'unrelated'/('a'*64))
            with self.assertRaisesRegex(ValueError,'location'): self.validate(bad)

    def test_nonzero_mandatory_pair_gate(self):
        self.warm['exit']=1
        with self.assertRaisesRegex(ValueError,'nonzero mandatory'): self.pair()

    def test_missing_mandatory_pair_gate(self):
        with self.assertRaisesRegex(ValueError,'missing mandatory'): p.validate_pair({'runs':{}},self.root,self.current)

    def test_cache_continuity(self):
        self.warm['cacheStart']['files']={}
        with self.assertRaisesRegex(ValueError,'continuity'): self.pair()

    def test_unmatched_artifact(self):
        self.clean['buildEnd']['files']={}
        with self.assertRaisesRegex(ValueError,'mandatory artifact'): self.validate()

    def test_corrupt_live_artifact(self):
        (self.build/'lib/lean/Solidity/Evm/Compiler.olean').write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError,'live artifacts'): self.validate()

    def test_corrupt_attachment(self):
        (self.root/'clean.runtime').write_text('{}')
        with self.assertRaisesRegex(ValueError,'corrupt'): self.validate()

    def test_missing_cap_swap_peak_tool_and_threads(self):
        for field,value in [('memoryMax',16*1024**3),('swapMax',1024),('memoryPeak',0),
                            ('realLeanSha256','e'*64),('lakeVersion','wrong'),('leanNumThreads','4')]:
            bad=copy.deepcopy(self.clean); data=json.loads((self.root/'clean.runtime').read_text()); data[field]=value
            bad['runtime']='bad.runtime'; bad['runtimeSha256']=self.attach('bad.runtime',json.dumps(data).encode())
            with self.assertRaises(ValueError,msg=field): self.validate(bad)

    def test_parallel_or_missing_samples(self):
        for data in [b'[]',b'[{"rssBytes":10,"leanWorkers":2}]']:
            self.clean['samplesSha256']=self.attach('clean.samples',data)
            with self.assertRaisesRegex(ValueError,'samples'): self.validate()

    def test_fetch_in_clean_log(self):
        self.clean['logSha256']=self.attach('clean.log',b'Fetched Solidity.Evm.Compiler')
        with self.assertRaisesRegex(ValueError,'fetch labeled clean'): self.validate()

    def test_unmatched_extra_live_artifact(self):
        (self.build/'extra').write_bytes(b'not inventoried')
        with self.assertRaisesRegex(ValueError,'live artifacts'): self.validate()

    def test_duplicate_attached_json(self):
        self.clean['runtimeSha256']=self.attach('clean.runtime',b'{"swapMax":1,"swapMax":0}')
        with self.assertRaisesRegex(ValueError,'duplicate JSON'): self.validate()

    def test_negative_and_noninteger_worker_counts(self):
        for workers in [-1,0.5,True]:
            data=json.dumps([{'rssBytes':10,'leanWorkers':workers}]).encode()
            self.clean['samplesSha256']=self.attach('clean.samples',data)
            with self.assertRaisesRegex(ValueError,'samples'): self.validate()

    def test_scoped_pair_cannot_satisfy_final_gate(self):
        row={'id':'cache-equivalence','revision':'1'*40,'command':['scoped-pair'],
             'exit':0,'status':'pass','log':'clean.log','sha256':self.clean['logSha256']}
        with self.assertRaisesRegex(ValueError,'scoped pair'):
            e.aggregate({'schema':1,'revision':'1'*40,'gates':[row]},self.root,'1'*40,['cache-equivalence'],self.current)

    def test_inventory_root_symlink(self):
        link=self.root/'link'; link.symlink_to(self.build,target_is_directory=True)
        with self.assertRaisesRegex(ValueError,'symlink'): p.inventory(link)

    def test_missing_or_changed_execution_budget_script(self):
        self.clean['executionScriptSha256']=self.attach('clean.sh',b'ordinary warm lake build')
        with self.assertRaisesRegex(ValueError,'execution script'): self.validate()

    def test_collect_create_timeout_retains_record_and_removes_config(self):
        with tempfile.TemporaryDirectory() as external:
            out=Path(external)/'collection'
            (self.root/'lakefile.toml').write_bytes(b'config')
            with patch.object(p,'ROOT',self.root), patch.object(p.e,'snapshot',return_value=self.current), \
                 patch('shutil.which',return_value='/usr/bin/true'), \
                 patch.object(p,'docker',side_effect=lambda *a,**kw: (_ for _ in ()).throw(subprocess.TimeoutExpired('docker create',5)) if a[0]=='create' else SimpleNamespace(stdout=b'')):
                code=p.collect(SimpleNamespace(out=out,gate='warm-compiler'))
            self.assertEqual(code,124)
            self.assertTrue((out/'provenance.json').is_file())
            self.assertFalse((self.root/'roadmap-v17-runtime.lakefile.toml').exists())

    def test_cleanup_and_changed_snapshot_failures_are_retained(self):
        with tempfile.TemporaryDirectory() as external:
            out=Path(external)/'collection'
            (self.root/'lakefile.toml').write_bytes(b'config')
            proc=MagicMock(); proc.poll.return_value=None; proc.wait.return_value=0
            def docker(*args,**kwargs):
                if args[0]=='create': return SimpleNamespace(stdout=b'owned-container')
                raise subprocess.TimeoutExpired('docker '+args[0],5)
            with patch.object(p,'ROOT',self.root), \
                 patch.object(p.e,'snapshot',side_effect=[self.current,ValueError('changed source')]), \
                 patch('shutil.which',return_value='/usr/bin/true'), patch.object(p,'docker',side_effect=docker), \
                 patch.object(p.subprocess,'Popen',return_value=proc):
                code=p.collect(SimpleNamespace(out=out,gate='warm-compiler'))
            self.assertEqual(code,125)
            record=e.load(out/'provenance.json')
            self.assertEqual(record['after'],{'error':'changed source'})
            errors=e.load(out/'execution-errors.json')
            self.assertIn('container cleanup',[x['phase'] for x in errors])
            self.assertFalse((self.root/'roadmap-v17-runtime.lakefile.toml').exists())
            proc.kill.assert_called_once()
            self.assertTrue(p.UNRESOLVED.exists())

    def test_created_running_exited_monitor_uses_required_pid_column(self):
        with tempfile.TemporaryDirectory() as external:
            out=Path(external)/'collection'
            (self.root/'lakefile.toml').write_bytes(b'config')
            proc=MagicMock(); proc.poll.return_value=0; proc.wait.return_value=0
            states=iter([b'created',b'running',b'exited'])
            def docker(*args,**kwargs):
                self.assertGreater(kwargs.get('timeout',0),0)
                if args[0]=='create': return SimpleNamespace(stdout=b'owned-container')
                if args[0]=='inspect': return SimpleNamespace(stdout=next(states))
                if args[0]=='top':
                    self.assertEqual(args[-1],'pid,comm,rss')
                    return SimpleNamespace(stdout=b'PID COMMAND RSS\n1 lean 10\n')
                return SimpleNamespace(stdout=b'')
            with patch.object(p,'ROOT',self.root), patch.object(p.e,'snapshot',return_value=self.current), \
                 patch('shutil.which',return_value='/usr/bin/true'), patch.object(p,'docker',side_effect=docker), \
                 patch.object(p.subprocess,'Popen',return_value=proc):
                self.assertEqual(p.collect(SimpleNamespace(out=out,gate='warm-compiler')),0)
            self.assertEqual(e.load(out/'samples.json'),[{'rssBytes':10240,'leanWorkers':1}])

    def test_unresolved_container_refuses_another_collection(self):
        p.UNRESOLVED.write_text(json.dumps({'container':'roadmap-v17-'+'a'*32}))
        with patch.object(p,'docker',return_value=SimpleNamespace(stdout=b'running')):
            with self.assertRaisesRegex(ValueError,'refusing overlap'): p.ensure_no_unresolved()
        self.assertTrue(p.UNRESOLVED.exists())
        with patch.object(p,'docker',return_value=SimpleNamespace(stdout=b'exited')): p.ensure_no_unresolved()
        self.assertFalse(p.UNRESOLVED.exists())

    def test_commented_timeout_or_appended_command_rejected(self):
        original=(self.root/'clean.sh').read_bytes()
        for data in [b'# '+original+b'\nlake build', original+b'\nlake build']:
            self.clean['executionScriptSha256']=self.attach('clean.sh',data)
            with self.assertRaisesRegex(ValueError,'execution script'): self.validate()

    def test_boolean_exit_rejected(self):
        self.clean['exit']=False
        with self.assertRaisesRegex(ValueError,'invalid provenance exit'): self.validate()

    def test_missing_c_or_changed_serializer_rejected(self):
        bad=copy.deepcopy(self.clean); del bad['serializers']['clang']
        with self.assertRaisesRegex(ValueError,'missing serialized'): self.validate(bad)
        ref=self.clean['serializers']['clang']; ref['sha256']=self.attach(ref['path'],b'#!/bin/sh\nexec clang "$@"\n')
        with self.assertRaisesRegex(ValueError,'changed tool serializer'): self.validate()

    def test_changed_native_tool_hash_rejected(self):
        self.clean['buildTools']['clang']['sha256']='f'*64
        with self.assertRaisesRegex(ValueError,'tool binaries'): self.validate()

    def test_unwrapped_or_changed_mount_cannot_validate(self):
        argv=e.loads((self.root/self.clean['dockerArgv']).read_bytes())
        index=next(i for i,arg in enumerate(argv) if 'clang-launcher' in arg)
        argv[index]=argv[index].replace('clang-launcher','unwrapped-clang')
        self.clean['dockerArgvSha256']=self.attach(self.clean['dockerArgv'],json.dumps(argv).encode())
        with self.assertRaisesRegex(ValueError,'Docker spawn'): self.validate()

    def test_observed_unwrapped_native_entrypoint_rejected(self):
        runtime=e.loads((self.root/'clean.runtime').read_bytes())
        runtime['entrypointHashes']['clang']=self.current['buildTools']['clang']['sha256']
        self.clean['runtimeSha256']=self.attach('clean.runtime',json.dumps(runtime).encode())
        with self.assertRaisesRegex(ValueError,'unwrapped runtime'): self.validate()

    def test_correct_but_unused_serializer_attachment_rejected(self):
        ref=self.clean['serializers']['clang']; data=(self.root/ref['path']).read_bytes()
        ref['path']='unused-good-launcher'; ref['sha256']=self.attach(ref['path'],data)
        with self.assertRaisesRegex(ValueError,'mounted source'): self.validate()

    def test_gate_log_or_exit_disagreement(self):
        row={'exit':1,'sha256':self.clean['logSha256'],'log':'clean.log','command':self.clean['command']}
        with self.assertRaisesRegex(ValueError,'disagreement'): p.validate(self.clean,self.root,self.current,'clean-compiler',row)


if __name__=='__main__': unittest.main()
