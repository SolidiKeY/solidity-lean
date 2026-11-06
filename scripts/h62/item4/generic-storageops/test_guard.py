"""Regression: termination handlers must never turn a guard stop into success."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

class GuardTest(unittest.TestCase):
    def test_timeout_cannot_pass(self):
        with tempfile.TemporaryDirectory() as d:
            log=Path(d)/"guard.log"
            script=Path(__file__).with_name("bounded.py")
            child="import signal,time,sys; signal.signal(signal.SIGTERM,lambda *_:sys.exit(0)); time.sleep(10)"
            p=subprocess.run([sys.executable,"-B",str(script),"--timeout","1","--log",str(log),"--",sys.executable,"-c",child],capture_output=True,text=True)
            self.assertEqual(p.returncode,124,p.stdout+p.stderr)
            metrics=json.loads(log.with_suffix(".log.json").read_text())
            self.assertEqual(metrics["stop"],"timeout")
            self.assertEqual(metrics["child_exit"],0)
            self.assertEqual(metrics["exit"],124)
    def test_regular_failure_propagates(self):
        with tempfile.TemporaryDirectory() as d:
            log=Path(d)/"guard.log"
            p=subprocess.run([sys.executable,"-B",str(Path(__file__).with_name("bounded.py")),"--log",str(log),"--",sys.executable,"-c","raise SystemExit(7)"],capture_output=True,text=True)
            self.assertEqual(p.returncode,7,p.stdout+p.stderr)

if __name__=="__main__": unittest.main()
