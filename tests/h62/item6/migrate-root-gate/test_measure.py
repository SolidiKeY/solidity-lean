"""Failure controls for process supervision and evidence preservation."""
import json
from pathlib import Path
import subprocess
import sys
import signal
import time
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
SCRIPT = ROOT/'scripts/h62/item6/migrate-root-gate/measure.py'


class MeasureControls(unittest.TestCase):
    def run_case(self, directory, command):
        output = Path(directory)/'result.json'
        proc = subprocess.run([sys.executable, str(SCRIPT), str(output), *command],
                              capture_output=True, text=True, timeout=20)
        return proc, json.loads(output.read_text())

    def test_success_and_refuse_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            proc, result = self.run_case(directory, [sys.executable, '-c', 'print("ok")'])
            self.assertEqual(proc.returncode, 0)
            self.assertEqual(result['exit'], 0)
            output = Path(directory)/'result.json'
            original = output.read_bytes()
            repeat = subprocess.run([sys.executable, str(SCRIPT), str(output), 'false'],
                                    capture_output=True, timeout=20)
            self.assertEqual(repeat.returncode, 2)
            self.assertEqual(output.read_bytes(), original)

    def test_launch_failure_has_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            proc, result = self.run_case(directory, ['/nonexistent/h62-command'])
            self.assertEqual(proc.returncode, 75)
            self.assertEqual(result['resource_stop'], 'launcher-or-monitor-error')
            self.assertIn('FileNotFoundError', result['error'])

    def test_surviving_child_is_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            code = 'import subprocess; subprocess.Popen(["sleep", "60"])'
            proc, result = self.run_case(directory, [sys.executable, '-c', code])
            self.assertEqual(proc.returncode, 75)
            self.assertEqual(result['resource_stop'], 'descendants-after-command-exit')

    def test_supervisor_sigterm_cleans_child_and_preserves_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)/'result.json'
            ready = Path(directory)/'pid'
            code = ('import os,time,pathlib; pathlib.Path('+repr(str(ready))+
                    ').write_text(str(os.getpid())); time.sleep(60)')
            supervisor = subprocess.Popen([sys.executable, str(SCRIPT), str(output),
                                           sys.executable, '-c', code],
                                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                for _ in range(100):
                    if ready.exists():
                        break
                    time.sleep(0.02)
                self.assertTrue(ready.exists(), 'child did not start')
                supervisor.send_signal(signal.SIGTERM)
                supervisor.communicate(timeout=10)
                self.assertEqual(supervisor.returncode, 75)
                result = json.loads(output.read_text())
                self.assertIn('SupervisorInterrupted', result['error'])
                self.assertFalse(Path('/proc/'+ready.read_text()).exists())
            finally:
                if supervisor.poll() is None:
                    supervisor.kill()
                    supervisor.wait()


    def test_sigterm_during_process_inspection_is_not_swallowed(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)/'result.json'
            ready = Path(directory)/'child-pid'
            child = ('import os,pathlib,time; pathlib.Path('+repr(str(ready))+
                     ').write_text(str(os.getpid())); time.sleep(60)')
            wrapper = """
import importlib.util, os, pathlib, signal, sys
spec = importlib.util.spec_from_file_location('h62_measure', SCRIPT_PATH)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
original_read = pathlib.Path.read_text
sent = False
def injected_read(path, *args, **kwargs):
    global sent
    if str(path).startswith('/proc/') and path.name == 'stat' and not sent:
        sent = True
        os.kill(os.getpid(), signal.SIGTERM)
    return original_read(path, *args, **kwargs)
pathlib.Path.read_text = injected_read
sys.argv = ['measure.py', OUTPUT_PATH, sys.executable, '-c', CHILD_CODE]
m.main()
""".replace('SCRIPT_PATH', repr(str(SCRIPT))).replace('OUTPUT_PATH', repr(str(output))).replace('CHILD_CODE', repr(child))
            try:
                proc = subprocess.run([sys.executable, '-B', '-c', wrapper],
                                      capture_output=True, text=True, timeout=10)
                self.assertEqual(proc.returncode, 75, proc.stderr)
                result = json.loads(output.read_text())
                self.assertIn('SupervisorInterrupted', result['error'])
                self.assertEqual(result['resource_stop'], 'launcher-or-monitor-error')
            finally:
                if ready.exists():
                    try:
                        import os
                        os.killpg(int(ready.read_text()), signal.SIGKILL)
                    except ProcessLookupError:
                        pass


if __name__ == '__main__':
    unittest.main()
