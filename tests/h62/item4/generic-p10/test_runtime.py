"""Exercise bounded command failure and orphan/TERM-resistant child cleanup."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[4]
GUARD = ROOT/'scripts/h62/item4/generic-p10/bounded.py'
sys.path.insert(0,str(ROOT/'scripts/h62/item4/generic-p10'))
from bounded import process_table
from measure import quiesce


class RuntimeTests(unittest.TestCase):
    def run_guard(self, directory, code, timeout=5):
        report = Path(directory)/'report.json'
        result = subprocess.run([sys.executable, '-B', str(GUARD), '--report', str(report),
            '--timeout', str(timeout), '--', sys.executable, '-c', code], timeout=20,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        return result, json.loads(report.read_text())

    def test_success_is_not_resource_stop(self):
        with tempfile.TemporaryDirectory() as directory:
            result, report = self.run_guard(directory, 'print("ordinary command")')
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIsNone(report['resource_stop'])
            self.assertGreaterEqual(report['minimum_available_bytes'], 4*1024**3)

    def test_child_failure_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            result, report = self.run_guard(directory, 'raise SystemExit(7)')
            self.assertEqual(result.returncode, 7, result.stdout)
            self.assertEqual(report['exit_code'], 7)

    def resistant_child(self, orphan):
        with tempfile.TemporaryDirectory() as directory:
            pidfile = Path(directory)/'worker.pid'
            worker = f'import os,signal,time,pathlib; signal.signal(signal.SIGTERM,signal.SIG_IGN); pathlib.Path({str(pidfile)!r}).write_text(str(os.getpid())); time.sleep(60)'
            launcher = f'import subprocess,sys,pathlib,time; subprocess.Popen([sys.executable,"-c",{worker!r}]); p=pathlib.Path({str(pidfile)!r})\nwhile not p.exists(): time.sleep(.01)\n'
            if not orphan: launcher += 'time.sleep(60)\n'
            result, report = self.run_guard(directory, launcher, timeout=1)
            self.assertEqual(result.returncode, 75, result.stdout)
            self.assertIn('launcher exited' if orphan else 'wall timeout', report['resource_stop'])
            pid = int(pidfile.read_text())
            for _ in range(20):
                try: state = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[0]
                except FileNotFoundError: break
                if state == 'Z': break
                time.sleep(0.05)
            else:
                os.kill(pid, 9)
                self.fail('TERM-resistant owned child survived guard')

    def test_orphan_after_successful_launcher_is_refused_and_killed(self):
        self.resistant_child(orphan=True)

    def test_timeout_kills_descendant_even_if_root_exits_after_term(self):
        self.resistant_child(orphan=False)

    def test_timed_out_client_can_quiesce_its_guard(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)
            pidfile=path/'child.pid'
            child=f'import os,time,pathlib;pathlib.Path({str(pidfile)!r}).write_text(str(os.getpid()));time.sleep(60)'
            guard=subprocess.Popen([sys.executable,'-B',str(GUARD),'--report',str(path/'guard.json'),
                '--',sys.executable,'-c',child],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
            try:
                deadline=time.monotonic()+5
                while not pidfile.exists() and time.monotonic()<deadline: time.sleep(.05)
                self.assertTrue(pidfile.exists())
                quiesce(dict(server_pid=guard.pid,server_started=process_table()[guard.pid]['started']),path)
                guard.wait(timeout=5)
                self.assertTrue(json.loads((path/'quiescence.json').read_text())['stopped'])
                self.assertEqual(json.loads((path/'guard.json').read_text())['termination_signal'],15)
            finally:
                if guard.poll() is None: guard.terminate();guard.wait(timeout=10)


if __name__ == '__main__': unittest.main()
