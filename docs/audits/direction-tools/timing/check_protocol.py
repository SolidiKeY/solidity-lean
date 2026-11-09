#!/usr/bin/env python3
"""Regression checks for default host safety and absent-measurement reporting.
python3 docs/audits/direction-tools/timing/check_protocol.py
No Lean, build, server, network, or source edits; temporary outputs only.
"""
import importlib.util,json,pathlib,subprocess,sys,tempfile
from unittest import mock
HERE=pathlib.Path(__file__).resolve().parent

def main():
    with tempfile.TemporaryDirectory(prefix='timing-protocol-') as work:
        root=pathlib.Path(work); forbidden=root/'must-not-exist'
        result=subprocess.run([sys.executable,str(HERE/'measure.py'),'--repo',str(root/'not-a-repository'),'--work',str(forbidden)],capture_output=True,text=True)
        assert result.returncode==2 and '--cloud-vm' in result.stderr
        assert not forbidden.exists(), 'default invocation wrote before opting in'
        result=subprocess.run([sys.executable,str(HERE/'references.py'),'--project','EvmYul','--refs',str(root/'refs-must-not-exist'),'--work',str(forbidden)],capture_output=True,text=True)
        assert result.returncode==2 and '--cloud-vm' in result.stderr
        assert not forbidden.exists() and not (root/'refs-must-not-exist').exists()
        spec=importlib.util.spec_from_file_location('timing_measure',HERE/'measure.py'); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
        try: mod.command(['this-command-must-not-run'],root,root/'must-not-write.log')
        except RuntimeError as e: assert '--cloud-vm' in str(e)
        else: raise AssertionError('unguarded command helper')
        assert not (root/'must-not-write.log').exists()
        real_read_text=pathlib.Path.read_text
        def no_swap_fixture(path,*args,**kwargs):
            if str(path)=='/proc/meminfo': return 'SwapTotal: 0 kB\nMemAvailable: 8388608 kB\n'
            return real_read_text(path,*args,**kwargs)
        # A surviving compiler must stop launch before creating or replacing logs.
        with mock.patch.object(mod.pathlib.Path,'read_text',no_swap_fixture), mock.patch.object(mod,'CLOUD_VM_OPT_IN',True), mock.patch.object(mod,'active_compilers',return_value=[12345]):
            try: mod.command(['this-command-must-not-run'],root,root/'overlap-must-not-write.log')
            except RuntimeError as e: assert 'refusing overlap' in str(e)
            else: raise AssertionError('foreign compiler was ignored')
        assert not (root/'overlap-must-not-write.log').exists()
        class FakeProcess:
            pid=999999
            def poll(self): return None
            def wait(self,timeout=None): return 0
        fake=FakeProcess()
        # Isolation failure after launch cleans up only our created session.
        with mock.patch.object(mod.pathlib.Path,'read_text',no_swap_fixture), mock.patch.object(mod,'CLOUD_VM_OPT_IN',True), mock.patch.object(mod,'active_compilers',side_effect=[[],PermissionError('scan denied')]), mock.patch.object(mod.subprocess,'Popen',return_value=fake), mock.patch.object(mod.os,'getpgid',return_value=0), mock.patch.object(mod.os,'killpg') as kill:
            try: mod.command(['fixture-only'],root,root/'scan-failure.log')
            except PermissionError: pass
            else: raise AssertionError('post-launch scan failure swallowed')
            assert kill.call_args_list==[mock.call(fake.pid,mod.signal.SIGTERM),mock.call(fake.pid,mod.signal.SIGKILL)], 'surviving descendants were not stopped'
        # Interrupt the real resume loop immediately after its first checkpoint.
        # No Lean or Git runs: these interfaces are replaced by deterministic fixtures.
        fixture=root/'resume-fixture'; fixture.mkdir(); source=fixture/'source'; source.mkdir(); output=fixture/'results'; output.mkdir()
        base=json.loads((HERE/'inventory.json').read_text())['base']
        versions={'lean':'fixture lean','lake':'fixture lake'}
        plan=[{'path':name+'.lean','area':'Other','lines':100} for name in ['A','B']]
        rows=[{'path':name+'.lean','status':'pass','cache':{'exit_code':0,'cwd':str(source)},'plain':{'exit_code':0,'cwd':str(source),'wall_seconds':1},'original_provenance':{'marker':name}} for name in ['A','B','C']]
        (fixture/'inventory.json').write_text(json.dumps({'base':base,'sample_plan':plan}))
        saved=output/'sample-results.json'; saved.write_text(json.dumps({'base':base,'versions':versions,'samples':rows}))
        def fake_output(command,**kwargs):
            if command[0] in versions: return versions[command[0]]+'\n'
            if 'rev-parse' in command: return base+'\n'
            if 'status' in command: return ''
            raise AssertionError('unexpected external command '+repr(command))
        def fake_command(command,cwd,log,timeout=600):
            return {'exit_code':0,'command':command,'cwd':str(cwd),'wall_seconds':0.01,'log':str(log)}
        original_write=mod.atomic_write_json
        class InterruptedAfterCheckpoint(BaseException): pass
        def interrupt_after_save(path,data):
            original_write(path,data)
            raise InterruptedAfterCheckpoint()
        with mock.patch.object(mod,'HERE',fixture), mock.patch.object(mod,'capture_environment',return_value={'swap_total_kib':0,'metadata_scope':'test fixture'}), mock.patch.object(mod.subprocess,'check_output',side_effect=fake_output), mock.patch.object(mod,'command',side_effect=fake_command), mock.patch.object(mod,'atomic_write_json',side_effect=interrupt_after_save), mock.patch.object(mod,'CLOUD_VM_OPT_IN',False), mock.patch.object(sys,'argv',['measure.py','--cloud-vm','--repo',str(source),'--work',str(output),'--only','A.lean']):
            try: mod.main()
            except InterruptedAfterCheckpoint: pass
            else: raise AssertionError('interruption fixture did not run')
        restored={row['path']:row for row in json.loads(saved.read_text())['samples']}
        assert set(restored)=={'A.lean','B.lean','C.lean'}
        assert restored['B.lean']==rows[1] and restored['C.lean']==rows[2], 'resume erased unprocessed or unplanned observations'
        target=fixture/'atomic.json'; target.write_text('{"keep": true}\n')
        with mock.patch.object(mod.os,'replace',side_effect=OSError('simulated rename failure')):
            try: original_write(target,{'replacement':True})
            except OSError: pass
            else: raise AssertionError('rename failure fixture did not run')
        assert json.loads(target.read_text())=={'keep':True}, 'failed checkpoint replaced existing data'

        # Profile provenance must match before rankings can be attached.
        inv=root/'fixture-inventory.json'; inv.write_text(json.dumps({'base':base,'largest_areas':[],'areas':{},'build_workloads':{},'incremental':[],'sample_plan':[]}))
        empty=root/'empty-sample.json'; empty.write_text(json.dumps({'base':base,'versions':{},'samples':[]}))
        wrong=root/'wrong-profile.json'; wrong.write_text(json.dumps({'base':'wrong-base'}))
        bad=subprocess.run([sys.executable,str(HERE/'analyze.py'),'--inventory',str(inv),'--sample',str(empty),'--profiles',str(wrong),'--repo',str(root),'--out',str(root/'bad-analysis')],capture_output=True,text=True)
        assert bad.returncode!=0 and 'profile dataset base mismatch' in bad.stderr
        assert not (root/'bad-analysis/analysis.json').exists()
        baseline=root/'baseline.json'; baseline.write_text(json.dumps({'base':base,'samples':[{'path':'Solidity.lean','status':'dependency-cache-unavailable'}]}))
        effective=root/'effective.json'; effective.write_text(json.dumps({'base':base,'per_area':[],'slowest_sampled_modules':[],'declaration_profiles':None,'full_check_only_estimates':{},'passing_current_modules':1,'attempted_observations':2,'current_gaps':[],'limitations':[]}))
        changed=subprocess.run([sys.executable,str(HERE/'summarize.py'),'--sample',str(baseline),'--analysis',str(effective),'--out',str(root/'effective-summary')],check=True,capture_output=True,text=True)
        effective_summary=json.loads((root/'effective-summary/summary.json').read_text())
        assert effective_summary['fresh_passing_samples']==1 and effective_summary['waits']==[]
        assert len(effective_summary['baseline_only_counts']['waits'])==1
        assert json.loads(changed.stdout)['passing']==1
        # Replay must never follow pre-existing output aliases to raw data.
        raw=root/'protected-input.json'; raw.write_text('{"keep": true}\n')
        for kind in ('symlink','hardlink'):
            alias=root/('alias-'+kind); alias.mkdir(); target=alias/'summary.json'
            if kind=='symlink': target.symlink_to(raw)
            else: target.hardlink_to(raw)
            denied=subprocess.run([sys.executable,str(HERE/'reproduce.py'),'--sample',str(raw),'--out',str(alias)],capture_output=True,text=True)
            assert denied.returncode==2 and '--out must be a new directory' in denied.stderr
            assert json.loads(raw.read_text())=={'keep':True}
        subprocess.run([sys.executable,str(HERE/'summarize.py'),'--out',str(root/'summary')],check=True,capture_output=True)
        summary=json.loads((root/'summary/summary.json').read_text())
        assert summary['measurement_environment'] is None
        assert summary['measurement_versions'] is None
        assert summary['fresh_attempted_samples']==summary['fresh_passing_samples']==0
        assert summary['full_build_estimate_seconds'] is None
        assert all(r['sample_seconds_per_kloc'] is None for r in summary['areas'])
    spec=importlib.util.spec_from_file_location('timing_profiles',HERE/'profiles.py'); profiles=importlib.util.module_from_spec(spec); spec.loader.exec_module(profiles)
    assert profiles.union_seconds([(0,1000),(500,1500)])==1.5
    assert profiles.union_seconds([(0,1000),(0,1000),(1000,2000)])==2
    print('PASS: cloud opt-in, absent-measurement reporting, interrupted-resume preservation, atomic failure safety, interval unions')
if __name__=='__main__': main()
