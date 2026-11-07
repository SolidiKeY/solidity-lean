#!/usr/bin/env python3
"""Guard held runtime scripts against stale delegates, substituted receipts and long waits.

Uses small file/process fixtures only. No Lean, Docker, native checker, WASM
build, stopped benchmark or cached verdict is executed.
"""
import ast
import ctypes
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

AREA=Path(__file__).parent

def load(name):
    spec=importlib.util.spec_from_file_location('repair_'+name,AREA/(name+'.py'))
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

baseline=load('baseline-inputs');timer=load('invocation-deadline')


class Controls(unittest.TestCase):
    def test_baseline_exact_bytes_and_mutation_missing_link_refusal(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp).resolve();raw=b'{"fixture":true}';pins={n:hashlib.sha256(raw).hexdigest() for n in baseline.EXPECTED}
            for n in pins:(root/n).write_bytes(raw)
            with patch.object(baseline,'EXPECTED',pins):
                result=baseline.load(root);self.assertEqual(len(result),3)
                name=next(iter(pins));(root/name).write_text('{}')
                with self.assertRaisesRegex(ValueError,'hash mismatch'):baseline.load(root)
                (root/name).unlink()
                with self.assertRaises(FileNotFoundError):baseline.load(root)
                (root/name).symlink_to(root/next(n for n in pins if n!=name))
                with self.assertRaises(OSError):baseline.load(root)
                (root/name).unlink();os.link(root/next(n for n in pins if n!=name),root/name)
                with self.assertRaisesRegex(ValueError,'unsafe'):baseline.load(root)

    def test_manifest_cannot_supply_new_pins_or_duplicate_json(self):
        with self.assertRaisesRegex(ValueError,'duplicate'):baseline.pairs([('x',1),('x',2)])
        self.assertEqual(len(baseline.EXPECTED),3)
        self.assertEqual(baseline.EXPECTED['native-stub-classification.json'],'8a144c8df84b05c23b0a366949e7bff9358667435f017d8c5fbd220cfca9c1c1')

    def test_closure_requires_explicit_baseline_before_any_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=subprocess.run(['python3',str(AREA/'scripts/closure-audit.py')],cwd=tmp,text=True,capture_output=True,timeout=3)
            self.assertEqual(p.returncode,2);self.assertIn('--baseline-evidence-dir',p.stderr)
            self.assertEqual(list(Path(tmp).iterdir()),[])
        text=(AREA/'scripts/closure-audit.py').read_text()
        self.assertNotIn("docs/benchmarks/directruntime-2026-11-04/before",text)

    def test_replay_timeout_units_and_no_cli_budget_waiver(self):
        tree=ast.parse((AREA/'scripts/native-negatives.py').read_text())
        seconds=[k.value.value for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='run' for k in n.keywords if k.arg=='timeout' and isinstance(k.value,ast.Constant)]
        self.assertEqual(seconds,[300])
        for budget in (True,0,300_000_000_001):
            with self.assertRaises(ValueError):timer.execute(lambda:None,budget_ns=budget)

    def test_real_action_zero_exit_and_failures(self):
        timer.execute(lambda:None,budget_ns=1_000_000_000)
        with self.assertRaises(RuntimeError):timer.execute(lambda:os.kill(os.getpid(),signal.SIGTERM),budget_ns=1_000_000_000)

    def test_real_timeout_reaps_owned_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            pidfile=Path(tmp)/'pid'
            def work():pidfile.write_text(str(os.getpid()));time.sleep(5)
            started=time.monotonic()
            with self.assertRaises(TimeoutError):timer.execute(work,budget_ns=100_000_000)
            self.assertLess(time.monotonic()-started,2)
            self.assertFalse(Path('/proc/'+pidfile.read_text()).exists())

    def test_real_parent_termination_kills_action_and_descendant(self):
        # Become a subreaper only in this test so orphan fixture grandchildren
        # can be reaped; cleanup uses pinned pidfds, never recycled numeric PIDs.
        libc=ctypes.CDLL(None,use_errno=True);previous=ctypes.c_int()
        if libc.prctl(37,ctypes.byref(previous),0,0,0)!=0:self.fail('GET_CHILD_SUBREAPER unavailable')
        if libc.prctl(36,1,0,0,0)!=0:self.fail('SET_CHILD_SUBREAPER unavailable')
        try:
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);supervisor=root/'supervisor.py'
                supervisor.write_text("import importlib.util,json,os,sys,time\nfrom pathlib import Path\ns=importlib.util.spec_from_file_location('timer',sys.argv[1]);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)\ndef action():\n child=os.fork()\n if child==0:\n  time.sleep(30);os._exit(0)\n ready=Path(sys.argv[2]);pending=ready.with_suffix('.pending');pending.write_text(json.dumps({'leader':os.getpid(),'descendant':child}));pending.replace(ready)\n time.sleep(30)\nm.execute(action)\n")
                for number in (signal.SIGTERM,signal.SIGHUP):
                    ready=root/('ready-'+str(number));pins={};identities={}
                    process=subprocess.Popen([sys.executable,str(supervisor),str((AREA/'invocation-deadline.py').resolve()),str(ready)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
                    try:
                        stop=time.monotonic()+3
                        while not ready.exists():
                            if process.poll() is not None or time.monotonic()>stop:self.fail('fixture supervisor did not become ready')
                            time.sleep(0.01)
                        identities=json.loads(ready.read_text())
                        for name,pid in identities.items():pins[name]=os.pidfd_open(pid)
                        os.kill(process.pid,number)
                        _,stderr=process.communicate(timeout=3)
                        self.assertNotEqual(process.returncode,0)
                        self.assertIn(b'supervisor interrupted',stderr)
                        self.assertFalse(Path('/proc/'+str(identities['leader'])).exists())
                        stop=time.monotonic()+3
                        while True:
                            child,status=os.waitpid(identities['descendant'],os.WNOHANG)
                            if child:
                                self.assertTrue(os.WIFSIGNALED(status));self.assertEqual(os.WTERMSIG(status),signal.SIGKILL);break
                            if time.monotonic()>stop:self.fail('fixture descendant survived supervisor termination')
                            time.sleep(0.01)
                    finally:
                        if process.poll() is None:process.kill();process.wait()
                        for fd in pins.values():
                            try:signal.pidfd_send_signal(fd,signal.SIGKILL)
                            except ProcessLookupError:pass
                            os.close(fd)
                        if 'descendant' in identities:
                            try:os.waitpid(identities['descendant'],0)
                            except ChildProcessError:pass
                        process.stdout.close();process.stderr.close()
        finally:
            if libc.prctl(36,previous.value,0,0,0)!=0:self.fail('restore child subreaper failed')

    def test_early_signal_cannot_start_action_after_group_cleanup_miss(self):
        libc=ctypes.CDLL(None,use_errno=True);previous=ctypes.c_int()
        self.assertEqual(libc.prctl(37,ctypes.byref(previous),0,0,0),0)
        self.assertEqual(libc.prctl(36,1,0,0,0),0)
        try:
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);script=root/'startup.py';before=root/'before';release=root/'release';group=root/'group';action=root/'action'
                script.write_text("import importlib.util,os,sys,time\nfrom pathlib import Path\ns=importlib.util.spec_from_file_location('timer',sys.argv[1]);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)\nbefore,release,group,action=map(Path,sys.argv[2:])\nreal_setsid=os.setsid\ndef delayed_group():\n pending=before.with_suffix('.pending');pending.write_text(str(os.getpid()));pending.replace(before)\n while not release.exists():time.sleep(.005)\n real_setsid();group.touch()\nm.os.setsid=delayed_group\nreal_killpg=os.killpg\ndef cleanup_miss(pid,number):\n try:return real_killpg(pid,number)\n except ProcessLookupError:\n  release.touch()\n  deadline=time.monotonic()+1\n  while not group.exists():\n   if time.monotonic()>deadline:raise RuntimeError('fixture group did not start')\n   time.sleep(.005)\n  time.sleep(.03)\n  raise\nm.os.killpg=cleanup_miss\ndef work():\n action.touch();time.sleep(30)\nm.execute(work)\n")
                process=subprocess.Popen([sys.executable,str(script),str((AREA/'invocation-deadline.py').resolve()),str(before),str(release),str(group),str(action)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
                descriptor=None;leader=None
                try:
                    end=time.monotonic()+3
                    while not before.exists():
                        if process.poll() is not None or time.monotonic()>end:self.fail('startup fixture not ready')
                        time.sleep(.005)
                    leader=int(before.read_text());descriptor=os.pidfd_open(leader)
                    os.kill(process.pid,signal.SIGTERM)
                    process.communicate(timeout=3)
                    self.assertNotEqual(process.returncode,0)
                    self.assertTrue(group.exists())  # created after killpg's ESRCH
                    self.assertFalse(action.exists())  # no parent ACK, no action
                    self.assertFalse(Path('/proc/'+str(leader)).exists())
                finally:
                    release.touch()
                    if process.poll() is None:process.kill();process.wait()
                    if descriptor is not None:
                        try:signal.pidfd_send_signal(descriptor,signal.SIGKILL)
                        except ProcessLookupError:pass
                        os.close(descriptor)
                    if leader is not None:
                        try:os.waitpid(leader,0)
                        except ChildProcessError:pass
                    process.stdout.close();process.stderr.close()
        finally:self.assertEqual(libc.prctl(36,previous.value,0,0,0),0)

    def test_zero_exit_overrun_cannot_publish_child_pass(self):
        spec=importlib.util.spec_from_file_location('negative_replay',AREA/'scripts/native-negatives.py')
        replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay)
        with tempfile.TemporaryDirectory() as tmp:
            pending=Path(tmp)/'pending.json';final=Path(tmp)/'results.json'
            def work():pending.write_text('{"passed":false,"status":"provisional"}')
            original=timer.os.waitpid
            def slow_reap(*args):
                result=original(*args);time.sleep(0.15);return result
            with patch.object(timer.os,'waitpid',side_effect=slow_reap):
                with self.assertRaises(TimeoutError):
                    timer.execute(work,budget_ns=100_000_000)
                    replay.publish_result(pending,final,time.monotonic_ns()+1_000_000_000)
            self.assertFalse(final.exists());self.assertFalse(json.loads(pending.read_text())['passed'])
            with self.assertRaises(TimeoutError):replay.publish_result(pending,final,0)
            self.assertFalse(final.exists())
            replay.publish_result(pending,final,time.monotonic_ns()+1_000_000_000)
            self.assertTrue(json.loads(final.read_text())['passed'])

    def test_existing_publication_paths_are_preserved(self):
        spec=importlib.util.spec_from_file_location('negative_replay_collision',AREA/'scripts/native-negatives.py')
        replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay)
        with tempfile.TemporaryDirectory() as tmp:
            pending=Path(tmp)/'pending';pending.write_text('{"passed":false,"status":"provisional"}')
            final=Path(tmp)/'results.json';temporary=Path(tmp)/'results.json.seal.tmp'
            temporary.write_text('preserve unexpected work')
            with self.assertRaises(FileExistsError):replay.publish_result(pending,final,time.monotonic_ns()+1_000_000_000)
            self.assertEqual(temporary.read_text(),'preserve unexpected work')
            temporary.unlink();final.write_text('preserve existing final')
            with self.assertRaises(FileExistsError):replay.publish_result(pending,final,time.monotonic_ns()+1_000_000_000)
            self.assertEqual(final.read_text(),'preserve existing final')

    def test_optimized_python_cannot_disable_validation_assertions(self):
        with tempfile.TemporaryDirectory() as tmp:
            for name in ('closure-audit.py','native-negatives.py','stack-symbols.py','capture-selected-c.py'):
                for flags,extra in ((['-O'],{}),([],{"PYTHONOPTIMIZE":"1"})):
                    child=subprocess.run(['python3',*flags,str(AREA/'scripts'/name)],cwd=tmp,env=dict(os.environ,**extra,NATIVE_BROWSER_SYMBOL_OUTPUT=str(Path(tmp)/'symbols')),capture_output=True,text=True,timeout=3)
                    self.assertNotEqual(child.returncode,0);self.assertIn('assertions enabled',child.stderr)
            self.assertEqual(list(Path(tmp).iterdir()),[])

    def test_publication_overrun_syncs_retraction_and_preserves_failed_rollback(self):
        spec=importlib.util.spec_from_file_location('negative_replay_sync',AREA/'scripts/native-negatives.py')
        replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay)
        with tempfile.TemporaryDirectory() as tmp:
            pending=Path(tmp)/'pending';pending.write_text('{"passed":false,"status":"provisional"}')
            final=Path(tmp)/'results.json';temporary=Path(tmp)/'results.json.seal.tmp'
            original=replay.os.fsync;directories=[]
            def spy(fd):
                if stat.S_ISDIR(os.fstat(fd).st_mode):directories.append(fd)
                return original(fd)
            with patch.object(replay.time,'monotonic_ns',side_effect=[0,0,2_000_000_000]),patch.object(replay.os,'fsync',side_effect=spy):
                with self.assertRaises(TimeoutError):replay.publish_result(pending,final,1_000_000_000)
            self.assertGreaterEqual(len(directories),2);self.assertFalse(final.exists());self.assertFalse(temporary.exists())
            directories.clear()
            def failed_rollback(fd):
                if stat.S_ISDIR(os.fstat(fd).st_mode):
                    directories.append(fd)
                    if len(directories)==2:raise OSError('fixture rollback fsync failure')
                return original(fd)
            with patch.object(replay.time,'monotonic_ns',side_effect=[0,0,2_000_000_000]),patch.object(replay.os,'fsync',side_effect=failed_rollback):
                with self.assertRaisesRegex(RuntimeError,'retraction unresolved'):replay.publish_result(pending,final,1_000_000_000)
            self.assertTrue(temporary.exists());self.assertFalse(json.loads(pending.read_text())['passed'])

    def test_delegates_are_tracked_and_baseline_parameter_is_required(self):
        expected={'proof-final.sh':['proof-gates-post-rebase.sh','axiom-gates-post-rebase.sh'],
                  'remaining-checks.sh':['closure-audit.py','native-negatives.py'],
                  'symbol-gate.sh':['stack-symbols.py']}
        for name,files in expected.items():
            text=(AREA/'scripts'/name).read_text()
            for f in files:
                self.assertIn('tests/directruntime-20261104/native-browser/readbounds/scripts/'+f,text)
                self.assertNotIn('.lake/native-browser-readbounds-6513/'+f,text)
        self.assertIn('--baseline-evidence-dir "$NATIVE_BROWSER_BASELINE_EVIDENCE"',(AREA/'scripts/remaining-checks.sh').read_text())
        self.assertIn('flock -u 9',(AREA/'scripts/remaining-checks.sh').read_text())

    def test_duplicate_wasm_entry_reaches_same_lock_before_setup_or_build(self):
        outer=(AREA/'wasm-build.sh').read_text();inner=(AREA/'scripts/wasm-build.sh').read_text()
        self.assertIn('exec bash "$script_dir/scripts/wasm-build.sh"',outer)
        self.assertLess(inner.index('flock 9'),inner.index('source /emsdk'))
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'scripts').mkdir();(root/'scripts/build-direct-runtime.py').write_text('from pathlib import Path;Path("built").touch()')
            (root/'outer.sh').write_text(outer)
            lock=root/'writer.lock';ready=root/'ready';setup=root/'setup.sh'
            setup.write_text('touch setup-ran\n')
            implementation=inner.replace('/tmp/solidity-lean-feature-groups-20261025/writer.lock',str(lock)).replace('/emsdk/emsdk_env.sh',str(setup))
            implementation=implementation.replace('flock 9','touch '+str(ready)+'\nflock 9')
            (root/'scripts/wasm-build.sh').write_text(implementation)
            with lock.open('w') as held:
                fcntl.flock(held,fcntl.LOCK_EX)
                child=subprocess.Popen(['bash',str(root/'outer.sh')],cwd=root,env=dict(os.environ,NATIVE_BROWSER_BOUNDED_GATE='1'),stdout=subprocess.PIPE,stderr=subprocess.PIPE)
                try:
                    stop=time.monotonic()+3
                    while not ready.exists():
                        if child.poll() is not None or time.monotonic()>stop:self.fail('builder did not reach lock')
                        time.sleep(0.01)
                    self.assertIsNone(child.poll());self.assertFalse((root/'setup-ran').exists());self.assertFalse((root/'built').exists())
                    fcntl.flock(held,fcntl.LOCK_UN)
                    stdout,stderr=child.communicate(timeout=3)
                    self.assertEqual(child.returncode,0,stderr.decode());self.assertTrue((root/'setup-ran').exists());self.assertTrue((root/'built').exists())
                finally:
                    if child.poll() is None:child.kill();child.wait()


if __name__=='__main__':unittest.main()
