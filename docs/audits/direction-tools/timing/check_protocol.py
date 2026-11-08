#!/usr/bin/env python3
"""Regression checks for default host safety and absent-measurement reporting.
python3 docs/audits/direction-tools/timing/check_protocol.py
No Lean, build, server, network, or source edits; temporary outputs only.
"""
import importlib.util,json,pathlib,subprocess,sys,tempfile
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
    print('PASS: cloud opt-in required before subprocess/output; absent measurements remain unknown')
if __name__=='__main__': main()
