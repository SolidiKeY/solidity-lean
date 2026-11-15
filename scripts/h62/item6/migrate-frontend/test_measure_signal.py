#!/usr/bin/env python3
"""Regression: signals arriving after spawn but before assignment reap the child."""
import importlib.util
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent


def worker(script, sig):
    spec = importlib.util.spec_from_file_location("measure", script)
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    real_popen = subprocess.Popen
    spawned = []

    def interrupt_before_assignment(*args, **kwargs):
        child = real_popen(*args, **kwargs)
        spawned.append(child)
        os.kill(os.getpid(), sig)
        return child

    with tempfile.TemporaryDirectory() as tmp, mock.patch.object(measure.subprocess, "Popen", interrupt_before_assignment):
        command = [sys.executable, "-c", "import time; time.sleep(60)"]
        if "migrate-frontend" in str(script):
            with mock.patch.object(measure, "available", return_value=8 * measure.GIB):
                result = measure.run(command, tmp, os.environ.copy(), Path(tmp) / "run.log")
            assert result["stop"].startswith("InterruptedError:")
        else:
            with mock.patch.object(measure, "resources", return_value=(8 * measure.GIB, 0, 0)), mock.patch.object(sys, "argv", [str(script), str(Path(tmp) / "result.json"), *command]):
                try:
                    measure.main()
                except SystemExit as exc:
                    assert exc.code == 75
                else:
                    raise AssertionError("expected resource-stop exit")
        assert len(spawned) == 1 and spawned[0].poll() is not None
        try:
            os.killpg(spawned[0].pid, 0)
        except ProcessLookupError:
            pass
        else:
            raise AssertionError("child process group survived")


class SignalRaceTest(unittest.TestCase):
    def test_signal_during_spawn(self):
        scripts = [HERE / "measure.py", HERE.parent / "migrate-root-gate" / "measure.py"]
        for script in scripts:
            for sig in (signal.SIGINT, signal.SIGTERM):
                with self.subTest(script=script, signal=sig):
                    subprocess.run([sys.executable, __file__, "worker", str(script), str(sig)], check=True, timeout=15)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "worker":
        worker(Path(sys.argv[2]), int(sys.argv[3]))
    else:
        unittest.main()
