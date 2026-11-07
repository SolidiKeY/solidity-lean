"""Guard leaked Syntax runner groups after signals, reserve/error stops or leader exit.

Only disposable Python children run. A TERM/INT-ignoring grandchild must die
before the serial writer lock becomes available; no Lean or baseline is run.
"""
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[4]
RUNNER = ROOT / "scripts/h62/item6/migrate-syntax/bounded.py"
GRANDCHILD = """import os,signal,sys,time
from pathlib import Path
signal.signal(signal.SIGTERM,signal.SIG_IGN)
signal.signal(signal.SIGINT,signal.SIG_IGN)
Path(sys.argv[1]).write_text(str(os.getpid()))
while True: time.sleep(.1)
"""
LEADER = """import subprocess,sys,time
from pathlib import Path
subprocess.Popen([sys.executable,'-c',sys.argv[2],sys.argv[1]])
while not Path(sys.argv[1]).exists(): time.sleep(.01)
if sys.argv[3]=='exit': raise SystemExit(0)
while True: time.sleep(.1)
"""
BOOT = """import importlib.util,sys
from pathlib import Path
sys.dont_write_bytecode=True
runner=Path(sys.argv[1]); sys.path.insert(0,str(runner.parent))
spec=importlib.util.spec_from_file_location('bounded_control',runner)
m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
m.LOCK_PATH=Path(sys.argv[2]); ready=Path(sys.argv[3]); mode=sys.argv[4]
def available():
    if ready.exists() and mode=='reserve': return 3*m.GIB
    if ready.exists() and mode=='error': raise OSError('guarded monitor failure')
    return 10*m.GIB
m.available=available
raise SystemExit(m.main(sys.argv[5:]))
"""


def live(pid):
    try:
        return Path('/proc',str(pid),'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X')
    except FileNotFoundError:
        return False


class BoundedControls(unittest.TestCase):
    def run_case(self, mode, sig=None):
        with tempfile.TemporaryDirectory() as temporary:
            directory=Path(temporary); ready=directory/'grandchild.pid'
            lock=directory/'writer.lock'; output=directory/'output'
            proc=subprocess.Popen([sys.executable,'-B','-c',BOOT,str(RUNNER),str(lock),str(ready),mode,
                                   '--output',str(output),'--',sys.executable,'-c',LEADER,str(ready),GRANDCHILD,
                                   'exit' if mode=='leader-exit' else 'wait'],
                                  stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
            grandchild=None
            try:
                deadline=time.monotonic()+8
                while not ready.exists() and proc.poll() is None and time.monotonic()<deadline:
                    time.sleep(.02)
                self.assertTrue(ready.exists(), 'fixture did not reach live grandchild')
                grandchild=int(ready.read_text()); group=os.getpgid(grandchild)
                self.assertTrue(live(grandchild))
                with lock.open('a') as handle:
                    with self.assertRaises(BlockingIOError):
                        fcntl.flock(handle,fcntl.LOCK_EX|fcntl.LOCK_NB)
                    if sig is not None:
                        proc.send_signal(sig)
                    # TERM cleanup has a two-second grace period: even after the
                    # leader exits, this ignoring grandchild keeps the lock held.
                    time.sleep(.35)
                    self.assertTrue(live(grandchild))
                    with self.assertRaises(BlockingIOError):
                        fcntl.flock(handle,fcntl.LOCK_EX|fcntl.LOCK_NB)
                _, stderr=proc.communicate(timeout=10)
                self.assertEqual(proc.returncode, 1, stderr.decode())
                self.assertFalse(live(grandchild))
                result=json.loads((output/'result.json').read_text())
                expected={'leader-exit':'surviving-descendants','signal':'signal-stop','reserve':'reserve-stop','error':'supervisor-error'}[mode]
                self.assertEqual(result['status'],expected)
                self.assertTrue(result['process_group_quiescent'])
                self.assertTrue(result['cleanup']['term_sent'])
                self.assertTrue(result['cleanup']['kill_sent'])
                if sig is not None: self.assertEqual(result['signal'],sig)
                with lock.open('a') as handle:
                    fcntl.flock(handle,fcntl.LOCK_EX|fcntl.LOCK_NB)
            finally:
                if proc.poll() is None:
                    proc.kill(); proc.wait()
                if grandchild is not None and live(grandchild):
                    os.killpg(group,signal.SIGKILL)
                if proc.stderr: proc.stderr.close()

    def test_success_and_launch_error_leave_no_owned_group(self):
        for command, expected in [([sys.executable, "-c", "pass"], "pass"),
                                  (["/nonexistent/guarded-runner-command"], "supervisor-error")]:
            with self.subTest(expected=expected), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                run = subprocess.run([sys.executable, '-B', '-c', BOOT, str(RUNNER),
                                      str(directory/'lock'), str(directory/'ready'), 'normal',
                                      '--output', str(directory/'output'), '--', *command],
                                     capture_output=True, text=True, timeout=10)
                result = json.loads((directory/'output/result.json').read_text())
                self.assertEqual(run.returncode, 0 if expected=='pass' else 1, run.stderr)
                self.assertEqual(result['status'], expected)
                self.assertTrue(result['process_group_quiescent'])
                self.assertFalse(result['cleanup']['kill_sent'])
                with (directory/'lock').open('a') as handle:
                    fcntl.flock(handle, fcntl.LOCK_EX|fcntl.LOCK_NB)

    def test_signals_reap_ignoring_descendants_before_unlock(self):
        for sig in (signal.SIGINT,signal.SIGTERM):
            with self.subTest(signal=sig): self.run_case('signal',sig)

    def test_normal_leader_exit_cannot_orphan_children(self):
        self.run_case('leader-exit')

    def test_reserve_stop_cleans_whole_group(self):
        self.run_case('reserve')

    def test_monitor_exception_cleans_whole_group(self):
        self.run_case('error')


if __name__=='__main__': unittest.main()
