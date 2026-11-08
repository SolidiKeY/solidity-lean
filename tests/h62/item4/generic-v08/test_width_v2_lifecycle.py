"""Owned-process read failures and real lock-lifetime regression fixtures.

The lightweight worker named lean is a process-control fixture, not a Lean proof.
"""
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
SCRIPTS = ROOT/'scripts/h62/item4/generic-v08'
sys.path.insert(0, str(SCRIPTS))
from width_resources import process_usage, MeasurementError
from width_scope import require_scope, ScopeError


class Measurement(unittest.TestCase):
    def setup_tree(self, root):
        for pid, parent in ((321, 1), (322, 321)):
            proc = root/str(pid)
            proc.mkdir(parents=True)
            (proc/'stat').write_text(str(pid)+' (lean) S '+str(parent))
            (proc/'status').write_text('Name: lean\nState: S\nVmRSS: 2 kB\n')

    def test_owned_tree_counts_all_reachable_processes(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.setup_tree(root)
            self.assertEqual(process_usage(321, root, lambda _: True), (4096, 2))

    def test_live_owned_child_read_errors_fail_closed(self):
        for pid in (321, 322):
            for error in (PermissionError, OSError):
                with self.subTest(pid=pid, error=error), tempfile.TemporaryDirectory() as folder:
                    root = Path(folder)
                    self.setup_tree(root)
                    target = root/str(pid)/'status'
                    original = Path.read_text
                    def read(path, *args, **kwargs):
                        if path == target:
                            raise error('live owned status unavailable')
                        return original(path, *args, **kwargs)
                    with patch.object(Path, 'read_text', read):
                        with self.assertRaises(MeasurementError):
                            process_usage(321, root, lambda _: True)

    def test_malformed_or_missing_live_rss_fails(self):
        for text in ('Name: lean\nVmRSS: invalid kB\n', 'Name: lean\nState: S\n'):
            with tempfile.TemporaryDirectory() as folder:
                root = Path(folder)
                self.setup_tree(root)
                (root/'322/status').write_text(text)
                with self.assertRaises(MeasurementError):
                    process_usage(321, root, lambda _: True)

    def test_missing_status_distinguishes_live_and_exited(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.setup_tree(root)
            (root/'322/status').unlink()
            with self.assertRaises(MeasurementError):
                process_usage(321, root, lambda _: True)
            self.assertEqual(process_usage(321, root, lambda pid: pid == 321), (2048, 1))

    def test_unreadable_process_discovery_fails(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.setup_tree(root)
            original = Path.iterdir
            def iterdir(path):
                if path == root:
                    raise PermissionError('process discovery unavailable')
                return original(path)
            with patch.object(Path, 'iterdir', iterdir):
                with self.assertRaises(MeasurementError):
                    process_usage(321, root, lambda _: True)

    def test_missing_cgroup_reports_unvalidated_lifecycle(self):
        original = Path.read_text
        def read(path, *args, **kwargs):
            if path == Path('/sys/fs/cgroup/memory.max'):
                raise FileNotFoundError('sandbox cgroup observation absent')
            return original(path, *args, **kwargs)
        fixture = Ownership('test_monitor_sigkill_cannot_orphan_worker')
        with patch.object(Path, 'read_text', read):
            with self.assertRaisesRegex(unittest.SkipTest, 'NOT VALIDATED'):
                fixture.setUp()


def running(pid):
    try:
        fields = dict(x.split(':', 1) for x in Path(f'/proc/{pid}/status').read_text().splitlines() if ':' in x)
        return not fields['State'].strip().startswith('Z')
    except FileNotFoundError:
        return False


def wait_for(predicate, seconds=10):
    deadline = time.monotonic()+seconds
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(.02)
    raise AssertionError('fixture did not reach expected lifecycle state')


@unittest.skipUnless(sys.platform == 'linux', 'Linux process/lock regression')
class Ownership(unittest.TestCase):
    def setUp(self):
        try:
            require_scope()
        except ScopeError as error:
            self.skipTest('hard resource scope unavailable; lifecycle NOT VALIDATED: '+str(error))

    def exercise(self, case):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            ready, term, release = root/'ready.json', root/'term', root/'release'
            record, lock = root/'record.json', root/'writer.lock'
            worker = root/'lean'
            worker.write_text('#!/usr/bin/env python3\n'+f'''
import os,signal,time,json
from pathlib import Path
release=Path({str(release)!r})
def stop(_signal,_frame):
    Path({str(term)!r}).touch()
    deadline=time.monotonic()+4
    while not release.exists() and time.monotonic()<deadline:
        time.sleep(.02)
    raise SystemExit(0)
signal.signal(signal.SIGTERM,stop)
lease_seen=any(os.path.realpath('/proc/self/fd/'+fd)=={str(lock)!r} for fd in os.listdir('/proc/self/fd'))
Path({str(ready)!r}).write_text(json.dumps(dict(worker=os.getpid(),monitor=os.getppid(),lease_seen=lease_seen)))
while True: time.sleep(.02)
''')
            worker.chmod(0o700)
            launcher = root/'monitor.py'
            launcher.write_text(f'''
import os,signal,subprocess,sys,time,runpy
from pathlib import Path
sys.path.insert(0,{str(SCRIPTS)!r})
real_spawn=subprocess.Popen
def interrupted_spawn(*args,**kwargs):
    child=real_spawn(*args,**kwargs)
    deadline=time.monotonic()+5
    while not Path({str(ready)!r}).exists() and time.monotonic()<deadline:
        time.sleep(.01)
    if not Path({str(ready)!r}).exists(): raise RuntimeError('worker never became ready')
    # Exact fork-to-assignment window: real child exists, caller proc is unset.
    os.kill(os.getpid(),signal.SIGTERM)
    return child
if {case!r}=='spawn-interrupt': subprocess.Popen=interrupted_spawn
sys.argv=[{str(SCRIPTS/'bounded.py')!r},*sys.argv[1:]]
runpy.run_path({str(SCRIPTS/'bounded.py')!r},run_name='__main__')
''')
            driver = root/'driver.py'
            driver.write_text(f'''
import sys,os,fcntl,importlib.util
from pathlib import Path
sys.path.insert(0,{str(SCRIPTS)!r})
spec=importlib.util.spec_from_file_location('driver',{str(SCRIPTS/'reproduce-width-v2.py')!r})
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
with Path({str(lock)!r}).open('a') as owner:
    fcntl.flock(owner,fcntl.LOCK_EX)
    command=[sys.executable,'-B',{str(launcher)!r},'--record',{str(record)!r},'--seconds','15',
        '--aggregate','--aggregate-parent','--parent-pid',str(os.getpid()),'--lease-fd',str(owner.fileno()),
        '--',{str(worker)!r},'-j1']
    try: result=module.run_monitor(command,pass_fds=(owner.fileno(),))
    except BaseException: raise SystemExit(1)
    raise SystemExit(result.returncode)
''')
            with (root/'output.log').open('w') as log:
                parent = subprocess.Popen([sys.executable, '-B', str(driver)], stdout=log, stderr=subprocess.STDOUT)
                pids = {}
                try:
                    wait_for(lambda: ready.exists() or parent.poll() is not None)
                    if not ready.exists():
                        self.fail('fixture exited before readiness: '+(root/'output.log').read_text())
                    pids = json.loads(ready.read_text())
                    self.assertTrue(pids['lease_seen'], 'worker must retain the writer lease itself')
                    if case == 'driver-term': parent.send_signal(signal.SIGTERM)
                    if case == 'driver-kill': parent.send_signal(signal.SIGKILL)
                    if case == 'monitor-kill': os.kill(pids['monitor'], signal.SIGKILL)
                    import fcntl
                    with lock.open('a') as contender:
                        if case == 'monitor-kill':
                            # Independent kernel guard must kill worker without monitor finally.
                            deadline = time.monotonic()+5
                            while running(pids['worker']):
                                try:
                                    fcntl.flock(contender, fcntl.LOCK_EX | fcntl.LOCK_NB)
                                except BlockingIOError:
                                    pass
                                else:
                                    self.assertFalse(running(pids['worker']), 'lease released while worker still active')
                                    fcntl.flock(contender, fcntl.LOCK_UN)
                                self.assertLess(time.monotonic(), deadline, 'orphaned worker after monitor kill')
                                time.sleep(.01)
                        else:
                            wait_for(term.exists)
                            self.assertTrue(running(pids['worker']))
                            with self.assertRaises(BlockingIOError):
                                fcntl.flock(contender, fcntl.LOCK_EX | fcntl.LOCK_NB)
                            release.touch()
                        wait_for(lambda: not running(pids['worker']) and not running(pids['monitor']))
                        fcntl.flock(contender, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        fcntl.flock(contender, fcntl.LOCK_UN)
                    parent.wait(timeout=5)
                    self.assertNotEqual(parent.returncode, 0)
                    if case != 'monitor-kill':
                        receipt = json.loads(record.read_text())
                        self.assertIsNotNone(receipt['stop'])
                        self.assertEqual(receipt['original_parent_pid'], parent.pid)
                        self.assertIsNotNone(receipt['worker_lease_fd'])
                        if case == 'driver-kill': self.assertEqual(receipt['stop'], 'parent-lost')
                    print('LIFECYCLE', case, 'worker lease retained, worker stopped before lock release')
                finally:
                    release.touch()
                    if parent.poll() is None:
                        parent.terminate()
                        try: parent.wait(timeout=7)
                        except subprocess.TimeoutExpired: parent.kill(); parent.wait()
                    for role in ('monitor', 'worker'):
                        pid = pids.get(role)
                        if pid is None: continue
                        try:
                            owned = str(root).encode() in Path(f'/proc/{pid}/cmdline').read_bytes()
                            if owned and running(pid):
                                os.kill(pid, signal.SIGTERM)
                                wait_for(lambda: not running(pid), seconds=7)
                        except FileNotFoundError:
                            pass

    def test_driver_termination_keeps_lock_until_worker_stops(self):
        for case in ('driver-term', 'driver-kill'):
            with self.subTest(case=case): self.exercise(case)

    def test_monitor_sigkill_cannot_orphan_worker(self):
        self.exercise('monitor-kill')

    def test_spawn_interruption_waits_until_handle_owned(self):
        self.exercise('spawn-interrupt')


if __name__ == '__main__':
    unittest.main()
