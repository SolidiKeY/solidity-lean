#!/usr/bin/env python3
"""Regression for the confirmed live-descendant cleanup hole (no Lean jobs)."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

class CleanupControl(unittest.TestCase):
    def test_launcher_exit_cannot_leave_ignoring_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            child = "import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(60)"
            launcher = "import subprocess,sys,time; subprocess.Popen([sys.executable,'-c'," + repr(child) + "]); time.sleep(.4)"
            cmd = [sys.executable, str(Path(__file__).with_name("bounded.py")),
                "--cwd", str(tmp), "--toolchain", "/workspace/h62-generic-yul-views/lean-4.35.0-linux",
                "--log", str(tmp/"job.log"), "--result", str(tmp/"result.json"),
                "--", sys.executable, "-c", launcher]
            p = subprocess.run(cmd, text=True, capture_output=True, timeout=20)
            self.assertEqual(p.returncode, 1, p.stdout+p.stderr)
            result = json.loads((tmp/"result.json").read_text())
            self.assertEqual(result["resource_stop"], "launcher exited with live descendants")
            self.assertTrue(result["process_group_quiescent"])
            group = result["process_group_id"]
            for proc in Path("/proc").glob("[0-9]*"):
                try:
                    fields=(proc/"stat").read_text().rsplit(")",1)[1].split()
                    self.assertFalse(int(fields[2]) == group and fields[0] != "Z", str(proc))
                except (FileNotFoundError, ProcessLookupError, PermissionError): pass

if __name__ == "__main__": unittest.main()
