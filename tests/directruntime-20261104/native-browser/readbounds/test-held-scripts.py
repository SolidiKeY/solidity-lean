#!/usr/bin/env python3
"""Guard held runtime scripts against stale delegates, substituted receipts and long waits.

Uses small file/process fixtures only. No Lean, Docker, native checker, WASM
build, stopped benchmark or cached verdict is executed.
"""
import ast
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import stat
import subprocess
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
            for name in ('closure-audit.py','native-negatives.py'):
                child=subprocess.run(['python3','-O',str(AREA/'scripts'/name)],cwd=tmp,capture_output=True,text=True,timeout=3)
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
