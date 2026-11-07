#!/usr/bin/env python3
"""Expected-failure controls for descendant cleanup and false-pass prevention."""
import json
import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[4]
evidence = Path(sys.argv[1]).resolve()
runner = Path(__file__).with_name("bounded.py")
child = "import os,signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); print('DESC',os.getpid(),flush=True); time.sleep(30)"
for tag, timeout, delay, expected_child in [
    ("guard-timeout-control", 1, 30, None),
    ("guard-zero-exit-control", 10, 0.7, 0),
]:
    command = "import subprocess,time; subprocess.Popen(" + repr([sys.executable,"-c",child]) + "); time.sleep(" + repr(delay) + ")"
    result = subprocess.run([sys.executable,str(runner),"--evidence",str(evidence),"--tag",tag,
        "--timeout",str(timeout),"--",sys.executable,"-c",command], cwd=root, capture_output=True,text=True)
    record = json.loads((evidence/(tag+".json")).read_text())
    assert json.loads(result.stdout) == record, "missing/freshness-mismatched runner result"
    assert result.returncode != 0 and record["gate_exit"] != 0 and record["status"] == "fail", record
    assert record["stop_reason"] is not None
    if expected_child is not None:
        assert record["child_exit"] == expected_child, record
    lines = (evidence/(tag+".log")).read_text().splitlines()
    pid = int(next(line for line in lines if line.startswith("DESC ")).split()[1])
    status = Path(f"/proc/{pid}/status")
    if status.exists():
        assert "State:\tZ" in status.read_text(), "live owned descendant leaked"
    print(tag+": PASS (expected gate failure; no live descendant; child_exit="+str(record["child_exit"])+")")
