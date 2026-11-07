#!/usr/bin/env python3
"""Repeat the same unchanged frozen file under the surrounding bounded runner."""
import argparse
import hashlib
import json
from pathlib import Path
import statistics
import subprocess
import time

p = argparse.ArgumentParser()
p.add_argument("--output", type=Path, required=True)
p.add_argument("--compare", type=Path)
a = p.parse_args()
root = Path(__file__).resolve().parents[4]
source = root/"Solidity/Backend/WorldCalls/Premises.lean"
command = ["lake", "env", "lean", "-j1", "--tstack=131072", str(source)]
samples = []
for _ in range(5):
    start = time.monotonic()
    subprocess.run(command, cwd=root, check=True, capture_output=True)
    samples.append(time.monotonic()-start)
result = dict(command=command, file_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
              samples_seconds=samples, median_seconds=statistics.median(samples),
              tree="existing frozen core unchanged; additive test modules outside library roots")
if a.compare:
    before = json.loads(a.compare.read_text())
    assert before["command"] == result["command"] and before["file_sha256"] == result["file_sha256"]
    result["delta_percent"] = 100*(result["median_seconds"]/before["median_seconds"]-1)
a.output.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps(result))
if result.get("delta_percent", 0) > 10:
    raise SystemExit("SLOWDOWN_STOP: exceeds 10 percent")
