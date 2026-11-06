"""Resource runner controls use small OS processes, never Lean/server."""
import importlib.util
from pathlib import Path
import os
import signal
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('measure',ROOT/'scripts/h62/item6/migrate-frontend/measure.py')
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

class MeasureControls(unittest.TestCase):
    def test_missing_executable_restores_signal_handlers(self):
        old={s:signal.getsignal(s) for s in (signal.SIGINT,signal.SIGTERM)}
        with tempfile.TemporaryDirectory() as tmp:
            row=m.run(['/this-executable-does-not-exist'],ROOT,dict(os.environ),Path(tmp)/'log')
        self.assertIsNone(row['exit'])
        self.assertIn('FileNotFoundError',row['stop'])
        self.assertEqual(old,{s:signal.getsignal(s) for s in old})

    def test_monitor_failure_cleans_up_child_group(self):
        old={s:signal.getsignal(s) for s in (signal.SIGINT,signal.SIGTERM)}
        original_popen=m.subprocess.Popen
        groups=[]
        def tracked_popen(*args,**kwargs):
            p=original_popen(*args,**kwargs)
            groups.append(p.pid)
            return p
        with tempfile.TemporaryDirectory() as tmp, patch.object(m.subprocess,'Popen',tracked_popen), patch.object(m,'usage',side_effect=InterruptedError('test monitor interrupted')):
            row=m.run([sys.executable,'-c','import time; time.sleep(30)'],ROOT,dict(os.environ),Path(tmp)/'log')
        self.assertIn('InterruptedError',row['stop'])
        self.assertEqual(old,{s:signal.getsignal(s) for s in old})
        for group in groups:
            with self.assertRaises(ProcessLookupError): os.killpg(group,0)

    def test_headroom_guard_fails_before_spawn(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(m,'available',return_value=0):
            with self.assertRaisesRegex(RuntimeError,'HEADROOM'):
                m.run([sys.executable,'-c','raise SystemExit(0)'],ROOT,dict(os.environ),Path(tmp)/'log')

if __name__=='__main__': unittest.main()
