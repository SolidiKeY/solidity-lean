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
    def test_driver_termination_keeps_lock_until_worker_stops(self):
        for termination in (signal.SIGTERM, signal.SIGKILL):
            with self.subTest(termination=termination), tempfile.TemporaryDirectory() as folder:
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
Path({str(ready)!r}).write_text(json.dumps(dict(worker=os.getpid(),monitor=os.getppid())))
while True: time.sleep(.02)
''')
                worker.chmod(0o700)
                driver = root/'driver.py'
                driver.write_text(f'''
import sys,os,fcntl,importlib.util
from pathlib import Path
sys.path.insert(0,{str(SCRIPTS)!r})
spec=importlib.util.spec_from_file_location('driver',{str(SCRIPTS/'reproduce-width-v2.py')!r})
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
with Path({str(lock)!r}).open('a') as owner:
    fcntl.flock(owner,fcntl.LOCK_EX)
    command=[sys.executable,'-B',{str(SCRIPTS/'bounded.py')!r},'--record',{str(record)!r},'--seconds','15',
        '--aggregate','--aggregate-parent','--parent-pid',str(os.getpid()),'--',{str(worker)!r},'-j1']
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
                            self.fail('fixture exited before worker readiness: '+(root/'output.log').read_text())
                        pids = json.loads(ready.read_text())
                        parent.send_signal(termination)
                        wait_for(term.exists)
                        self.assertTrue(running(pids['worker']))
                        import fcntl
                        with lock.open('a') as contender:
                            with self.assertRaises(BlockingIOError):
                                fcntl.flock(contender, fcntl.LOCK_EX | fcntl.LOCK_NB)
                            release.touch()
                            wait_for(lambda: record.exists() and not running(pids['worker']))
                            wait_for(lambda: not running(pids['monitor']))
                            fcntl.flock(contender, fcntl.LOCK_EX | fcntl.LOCK_NB)
                            fcntl.flock(contender, fcntl.LOCK_UN)
                        parent.wait(timeout=5)
                        receipt = json.loads(record.read_text())
                        self.assertIsNotNone(receipt['stop'])
                        self.assertEqual(receipt['original_parent_pid'], parent.pid)
                        if termination == signal.SIGKILL:
                            self.assertEqual(receipt['stop'], 'parent-lost')
                        print('LIFECYCLE', termination.name, 'lock retained through worker cleanup', receipt['stop'])
                    finally:
                        release.touch()
                        if parent.poll() is None:
                            parent.terminate()
                            try: parent.wait(timeout=7)
                            except subprocess.TimeoutExpired: parent.kill(); parent.wait()
                        for role in ('monitor', 'worker'):
                            pid = pids.get(role)
                            if pid is None:
                                continue
                            try:
                                owned = str(root).encode() in Path(f'/proc/{pid}/cmdline').read_bytes()
                                if owned and running(pid):
                                    os.kill(pid, signal.SIGTERM)
                                    wait_for(lambda: not running(pid), seconds=7)
                            except FileNotFoundError:
                                pass


if __name__ == '__main__':
    unittest.main()
