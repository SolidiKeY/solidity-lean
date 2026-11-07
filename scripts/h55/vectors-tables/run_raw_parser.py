#!/usr/bin/env python3
"""Run the Lean built-in parser probe with one process and memory reserve."""
import argparse
import json
import os
import signal
import subprocess
import time
from pathlib import Path
import raw_census as raw

LEAN = "/workspace/.setup/tools/lean-4.24.0-linux/bin/lean"
def available_kib():
    with open("/proc/meminfo") as f: host = int(next(line.split()[1] for line in f if line.startswith("MemAvailable:")))
    limit = Path("/sys/fs/cgroup/memory.max").read_text().strip()
    current = int(Path("/sys/fs/cgroup/memory.current").read_text())
    return min(host, (int(limit) - current) // 1024) if limit != "max" else host

def main():
    p=argparse.ArgumentParser(); p.add_argument("output", type=Path); a=p.parse_args()
    target=a.output.resolve()
    if target.exists() or target.is_relative_to(raw.ROOT): raise ValueError("new external output required")
    inventory=raw.collect(raw.ROOT)
    if raw.summary(inventory) != json.loads(raw.MANIFEST.read_text()): raise ValueError("source inventory differs")
    if available_kib()<4194304: raise RuntimeError("less than 4 GiB available")
    cmd=[LEAN,"-j1","--tstack=131072","--run","scripts/h55/vectors-tables/ParseProbe.lean"]+["Solidity/Yul/"+name for name in inventory]
    with target.open("x") as out:
        with subprocess.Popen(cmd,cwd=raw.ROOT,env=dict(os.environ,LEAN_NUM_THREADS="1"),stdout=out,stderr=subprocess.STDOUT,start_new_session=True) as proc:
            while proc.poll() is None:
                if available_kib()<4194304:
                    os.killpg(proc.pid,signal.SIGTERM); proc.wait(); raise RuntimeError("resource guard stopped parser")
                time.sleep(0.5)
            if proc.returncode: raise RuntimeError(f"parser exited {proc.returncode}")
    print(f"PASS: parser exited 0 for {len(inventory)} files; log {target}")

if __name__ == "__main__": main()
