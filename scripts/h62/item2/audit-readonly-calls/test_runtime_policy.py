"""Guard host fallback, reserve/swap weakening and unobserved escaped children."""
import importlib.util
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

spec=importlib.util.spec_from_file_location('runtime_policy_controls',Path(__file__).with_name('runtime_policy.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class RuntimePolicyControls(unittest.TestCase):
    def fixture(self, directory):
        root=Path(directory);proc=root/'proc';cg=root/'cg'
        (proc/'self').mkdir(parents=True)
        (proc/'self/cgroup').write_text('0::/job/leaf\n')
        (proc/'self/mountinfo').write_text(f'1 0 0:1 / {cg} rw - cgroup2 cgroup rw\n')
        (proc/'meminfo').write_text(f'MemAvailable: {13*1024**2} kB\nSwapTotal: {8*1024**2} kB\n')
        for node in [cg,cg/'job',cg/'job/leaf']:
            node.mkdir(parents=True,exist_ok=True)
            for name,value in {'memory.max':'max','memory.current':'1','memory.swap.max':'max','memory.swap.current':'0'}.items():(node/name).write_text(value)
        (cg/'job/memory.max').write_text(str(m.CAP));(cg/'job/memory.swap.max').write_text('0')
        return proc,cg

    def test_effective_ancestor_guards_and_host_swap_isolation(self):
        with tempfile.TemporaryDirectory() as tmp:
            proc,cg=self.fixture(tmp)
            (cg/'memory.swap.current').write_text('1234')
            guard=m.Guards('host',proc)
            self.assertEqual(guard.initial['limit'],m.CAP)
            self.assertEqual(guard.initial['reserve'],12*m.GIB)
            (cg/'job/memory.swap.current').write_text('1')
            with self.assertRaisesRegex(ValueError,'scoped swap'):guard.sample()

    def test_host_refuses_unbounded_swapping_or_insufficient_reserve(self):
        for field,value,reason in [('memory.max','max','memory cap'),('memory.swap.max','max','zero-swap')]:
            with self.subTest(field=field),tempfile.TemporaryDirectory() as tmp:
                proc,cg=self.fixture(tmp);(cg/'job'/field).write_text(value)
                with self.assertRaisesRegex(ValueError,reason):m.Guards('host',proc)
        with tempfile.TemporaryDirectory() as tmp:
            proc,cg=self.fixture(tmp);guard=m.Guards('host',proc)
            (proc/'meminfo').write_text('MemAvailable: 10485760 kB\nSwapTotal: 8388608 kB\n')
            with self.assertRaisesRegex(ValueError,'12GiB'):guard.sample()

    def test_real_mount_root_without_limit_file_needs_scoped_guards(self):
        with tempfile.TemporaryDirectory() as tmp:
            proc,cg=self.fixture(tmp);(cg/'memory.max').unlink()
            self.assertEqual(m.Guards('host',proc).initial['limit'],m.CAP)
            (cg/'job/memory.max').write_text('max')
            with self.assertRaisesRegex(ValueError,'memory cap'):m.Guards('host',proc)

    def test_membership_changes_and_bad_mounts_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            proc,cg=self.fixture(tmp);guard=m.Guards('host',proc)
            (proc/'self/cgroup').write_text('0::/job\n')
            with self.assertRaisesRegex(ValueError,'changed'):guard.sample()
            (proc/'self/cgroup').write_text('2:memory:/job\n')
            with self.assertRaisesRegex(ValueError,'unified'):m.effective_cgroup(proc)

    def test_original_vm_guards_remain(self):
        with tempfile.TemporaryDirectory() as tmp:
            proc,cg=self.fixture(tmp)
            (cg/'memory.max').write_text(str(16*m.GIB));(proc/'meminfo').write_text('MemAvailable: 1048576 kB\nSwapTotal: 0 kB\n')
            guard=m.Guards('vm',proc,cg)
            self.assertEqual(guard.initial['reserve'],4*m.GIB)
            (cg/'memory.current').write_text(str(12*m.GIB))
            with self.assertRaisesRegex(ValueError,'4GiB'):guard.sample()
            (cg/'memory.current').write_text('1');(proc/'meminfo').write_text('SwapTotal: 1 kB\n')
            with self.assertRaisesRegex(ValueError,'VM swap'):guard.sample()

    def test_sdk_explicit_host_no_fallback_and_toolchain_checks(self):
        with self.assertRaisesRegex(ValueError,'explicit'):m.sdk_configuration('host',None,Path('/nonexistent'))
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);sdk=root/'sdk';(sdk/'bin').mkdir(parents=True)
            (root/'lean-toolchain').write_text('leanprover/lean4:v4.24.0\n')
            for name in ['lean','lake']:(sdk/'bin'/name).write_bytes(b'configured-binary')
            good=['Lean (version 4.24.0, commit '+m.COMMIT+', Release)','Lake version 5.0.0-src+797c613',str(sdk)]
            with patch.object(m.subprocess,'check_output',side_effect=good):
                selected,record=m.sdk_configuration('host',sdk,root)
                self.assertEqual(selected,sdk);self.assertEqual(record['lean_commit'],m.COMMIT)
            for index,bad in [(0,'Lean version 4.35.0'),(1,'Lake another commit'),(2,str(root/'other'))]:
                outputs=good.copy();outputs[index]=bad
                with patch.object(m.subprocess,'check_output',side_effect=outputs),self.assertRaises(ValueError):m.sdk_configuration('host',sdk,root)
            (root/'lean-toolchain').write_text('leanprover/lean4:v4.35.0')
            with self.assertRaisesRegex(ValueError,'unapproved'):m.sdk_configuration('host',sdk,root)
            with self.assertRaisesRegex(ValueError,'no fallback'):m.sdk_configuration('host',root/'missing',root)

    def test_serial_argv_sdk_and_proof_deadline(self):
        row={'exe':'lean','exe_path':'/configured/lean','argv':['lean','-j1','Proof.lean'],'pid':7,'start':'5'}
        started={}
        self.assertIsNone(m.serial_reason([row],0,started,10,'/configured/lean'))
        self.assertIn('deadline',m.serial_reason([row],11,started,10,'/configured/lean'))
        self.assertIn('multiple',m.serial_reason([row,row],0,{},10))
        self.assertIn('SDK mismatch',m.serial_reason([row],0,{},10,'/other/lean'))
        for argv in [['lean','Proof.lean'],['lean','-j1','-j8'],['lean','-j1','--threads=8']]:
            self.assertIn('-j1',m.serial_reason([{**row,'argv':argv}],0,{},10))

    def test_crash_reservation_and_stable_task_window(self):
        from types import SimpleNamespace
        with tempfile.TemporaryDirectory() as tmp,patch.object(m.pwd,'getpwuid',return_value=SimpleNamespace(pw_dir=tmp)):
            with patch.dict(os.environ,{'HOME':tmp+'/fake1','XDG_STATE_HOME':tmp+'/other1'}):
                first=m.AggregateWindow();path=first.path;self.assertEqual(first.reserve(100),100)
            with patch.dict(os.environ,{'HOME':tmp+'/fake2','XDG_STATE_HOME':tmp+'/other2'}):
                with self.assertRaisesRegex(ValueError,'incomplete prior'):m.AggregateWindow()
            first.finish(7)
            second=m.AggregateWindow();self.assertEqual(second.path,path);self.assertEqual(second.spent,7)
            second.reserve(100);second.finish(m.WINDOW)
            with self.assertRaisesRegex(ValueError,'exhausted'):m.AggregateWindow()

    def test_cleanup_observation_failure_retries_without_unwind(self):
        class Tracker:
            known={}
            calls=0
            def sample(self):
                self.calls+=1
                if self.calls<3:raise ValueError('forced proc read failure')
                return []
        tracker=Tracker();notes=[]
        with patch.object(m.os,'killpg') as kill:
            failures=m.drain_owned(tracker,987654,sleeper=lambda seconds:None,note=notes.append)
        self.assertEqual(tracker.calls,3);self.assertEqual(kill.call_count,2)
        self.assertEqual(len(failures),2);self.assertEqual(len(notes),1)

    def test_optimized_preflight_still_rejects_nonserial_lean(self):
        runner=Path(__file__).with_name('bounded.py')
        with tempfile.TemporaryDirectory() as tmp:
            for tail in [['lean','Proof.lean'],['lean','-j1','-j8','Proof.lean']]:
                cmd=[sys.executable,'-B','-O',str(runner),'--evidence',tmp,'--tag','refuse','--']+tail
                result=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
                self.assertNotEqual(result.returncode,0)
                self.assertIn('direct Lean requires explicit -j1',result.stdout)
                self.assertFalse((Path(tmp)/'refuse.log').exists())

    def test_sdk_reaches_both_compiler_helpers_without_host_fallback(self):
        root=Path(__file__).resolve().parents[4]
        files=['scripts/h62/item1/readonly-bind/check_encoding_fixture.py','scripts/h62/item2/audit-readonly-calls/command_surface.py']
        for file in files:
            code="import importlib.util; s=importlib.util.spec_from_file_location('sdk_adapter',"+repr(str(root/file))+"); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); print(m.LEAN)"
            env={**os.environ,'AUDIT_RESOURCE_MODE':'host','AUDIT_LEAN_SDK':'/configured.sdk'}
            done=subprocess.run([sys.executable,'-B','-c',code],env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
            self.assertEqual(done.returncode,0,done.stderr);self.assertEqual(done.stdout.strip(),'/configured.sdk/bin/lean')
            env.pop('AUDIT_LEAN_SDK')
            refused=subprocess.run([sys.executable,'-B','-c',code],env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
            self.assertNotEqual(refused.returncode,0);self.assertIn('explicitly configured SDK',refused.stderr)

    def test_signal_after_popen_before_monitor_cleans_child(self):
        import textwrap
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);runner=Path(__file__).with_name('bounded.py').resolve()
            code=textwrap.dedent("""
                import hashlib,importlib.util,os,signal,subprocess,sys
                from pathlib import Path
                from unittest.mock import patch
                root=Path(ROOT_LITERAL);sdk=root/'sdk';(sdk/'bin').mkdir(parents=True)
                for name in ['lean','lake']:(sdk/'bin'/name).write_bytes(b'test-only-sdk')
                spec=importlib.util.spec_from_file_location('launch_test',RUNNER_LITERAL)
                m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
                class Guard:
                    initial={'test_only':True}
                    def sample(self):return self.initial
                digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
                meta={'lean_version':'test-only','lake_version':'test-only','sdk_root':str(sdk),'lean_commit':'test-only','lean_binary_sha256':digest(sdk/'bin/lean'),'lake_binary_sha256':digest(sdk/'bin/lake'),'toolchain_file_sha256':digest(m.ROOT/'lean-toolchain')}
                original=subprocess.Popen;window=m.policy.AggregateWindow
                def launch(*args,**kwargs):
                    child=original(*args,**kwargs)
                    if args[0][0]==sys.executable and args[0][-1]=='import time; time.sleep(30)':
                        (root/'child-pid').write_text(str(child.pid))
                        os.kill(os.getpid(),signal.SIGTERM)
                    return child
                sys.argv=['bounded','--evidence',str(root/'evidence'),'--tag','launch','--timeout','10','--',sys.executable,'-c','import time; time.sleep(30)']
                with patch.object(m.policy,'Guards',return_value=Guard()),patch.object(m.policy,'sdk_configuration',return_value=(sdk,meta)),patch.object(m.policy,'AggregateWindow',side_effect=lambda:window(root/'state')),patch.object(m.subprocess,'Popen',side_effect=launch):
                    m.main()
            """).replace('ROOT_LITERAL',repr(str(root))).replace('RUNNER_LITERAL',repr(str(runner)))
            child=None
            try:
                done=subprocess.run([sys.executable,'-B','-c',code],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=10)
                self.assertNotEqual(done.returncode,0,done.stdout)
                self.assertIn('monitor signal',done.stdout)
                child=int((root/'child-pid').read_text())
                self.assertFalse(Path('/proc',str(child)).exists(),done.stdout)
            finally:
                if child is None and (root/'child-pid').exists():child=int((root/'child-pid').read_text())
                if child is not None:
                    try:os.kill(child,signal.SIGKILL)
                    except ProcessLookupError:pass

    def test_first_seen_unreadable_orphan_is_not_silently_dropped(self):
        with tempfile.TemporaryDirectory() as tmp:
            proc=Path(tmp);pid=765432;entry=proc/str(pid);entry.mkdir()
            fields=['S',str(os.getpid()),'888888','0']+['0']*15+['777']
            (entry/'stat').write_text(str(pid)+' (nondumpable) '+' '.join(fields))
            tracker=m.Descendants(999999,proc)
            # Missing mandatory status is equivalent to an unreadable detail:
            # ownership is established and retained before the refusal.
            with self.assertRaisesRegex(ValueError,'owned detailed'):tracker.sample()
            self.assertEqual(tracker.known[pid],'777')
            (entry/'stat').unlink()
            with self.assertRaisesRegex(ValueError,'owned basic'):tracker.sample()

    def test_guard_executes_retained_source_not_matching_stale_pyc(self):
        import importlib.util
        import py_compile
        import shutil
        import struct
        with tempfile.TemporaryDirectory() as tmp:
            folder=Path(tmp)/'scripts/h62/item2/audit';folder.mkdir(parents=True)
            runner=folder/'bounded.py';policy=folder/'runtime_policy.py'
            shutil.copy2(Path(__file__).with_name('bounded.py'),runner)
            shutil.copy2(Path(__file__).with_name('runtime_policy.py'),policy)
            evil=Path(tmp)/'stale.py';evil.write_text('raise SystemExit(0)')
            cache=Path(importlib.util.cache_from_source(str(policy)));cache.parent.mkdir()
            py_compile.compile(str(evil),cfile=str(cache),dfile=str(policy),doraise=True,invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP)
            data=bytearray(cache.read_bytes());data[8:16]=struct.pack('<II',int(policy.stat().st_mtime),policy.stat().st_size);cache.write_bytes(data)
            done=subprocess.run([sys.executable,'-B',str(runner),'--evidence',str(Path(tmp)/'out'),'--tag','pyc','--','lean','Proof.lean'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            self.assertNotEqual(done.returncode,0);self.assertIn('direct Lean requires explicit -j1',done.stdout)

    def test_escaped_orphan_descendant_remains_observed(self):
        m.subreaper()
        code='import subprocess,sys; p=subprocess.Popen([sys.executable,"-c","import time; time.sleep(20)"],start_new_session=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL); print(p.pid,flush=True)'
        parent=subprocess.Popen([sys.executable,'-c',code],start_new_session=True,stdout=subprocess.PIPE,text=True)
        child=int(parent.stdout.readline());parent.wait(timeout=3)
        try:
            members=m.Descendants(parent.pid).sample()
            self.assertIn(child,{r['pid'] for r in members})
            self.assertNotEqual(os.getpgid(child),parent.pid)
        finally:
            os.kill(child,signal.SIGKILL);os.waitpid(child,0);parent.stdout.close()

if __name__=='__main__':unittest.main()
