#!/usr/bin/env python3
"""An exceptional memory guard must not orphan its real subprocess."""
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import bounded_lean


class RunnerTests(unittest.TestCase):
    def test_guard_exception_terminates_and_reaps_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root/"Fixture.lean").write_text("namespace Fixture\nend Fixture\n")
            (root/"bin").mkdir()
            lean = root/"bin"/"lean"
            lean.write_text("#!/usr/bin/env python3\nimport time\ntime.sleep(30)\n")
            lean.chmod(0o755)
            children = []
            real_popen = subprocess.Popen
            def spawn(*args, **kwargs):
                child = real_popen(*args, **kwargs)
                children.append(child)
                return child
            argv = ["bounded_lean.py", "--repo", str(root), "--toolchain", str(root),
                    "--artifacts", str(root/"artifacts"), "Fixture"]
            old_handlers = {s: signal.getsignal(s) for s in (signal.SIGINT, signal.SIGTERM)}
            try:
                with patch.object(sys, "argv", argv), \
                     patch("bounded_lean.available", side_effect=[8*1024**3, RuntimeError("swap detected")]), \
                     patch("bounded_lean.subprocess.Popen", side_effect=spawn):
                    with self.assertRaisesRegex(RuntimeError, "swap detected"):
                        bounded_lean.main()
                self.assertEqual(len(children), 1)
                self.assertIsNotNone(children[0].poll())
                with self.assertRaises(ChildProcessError): os.waitpid(children[0].pid, os.WNOHANG)
            finally:
                for s, handler in old_handlers.items(): signal.signal(s, handler)
                for child in children: bounded_lean.terminate(child)

if __name__ == "__main__": unittest.main()
