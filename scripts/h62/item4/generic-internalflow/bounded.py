#!/usr/bin/env python3
"""Single owned process group; 12 GiB per-process address cap, sampled group RSS/reserve guard, no swap.
Logs resource stops as failure. Never kills a process outside its own group.
"""
import argparse
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

ap = argparse.ArgumentParser()
ap.add_argument("--seconds", type=int, default=300)
ap.add_argument("command", nargs=argparse.REMAINDER)
a = ap.parse_args()
command = a.command[1:] if a.command[:1] == ["--"] else a.command
if not command:
    ap.error("command required")
def prepare():
    os.setsid()
    resource.setrlimit(resource.RLIMIT_AS, (12 * 1024**3, 12 * 1024**3))
    resource.setrlimit(resource.RLIMIT_CPU, (a.seconds, a.seconds))
env = dict(os.environ, LEAN_NUM_THREADS="1")
started = time.monotonic()
def reserve():
    avail = int(next(line.split()[1] for line in Path("/proc/meminfo").read_text().splitlines() if line.startswith("MemAvailable:"))) * 1024
    try:
        cap = int(Path("/sys/fs/cgroup/memory.max").read_text())
        current = int(Path("/sys/fs/cgroup/memory.current").read_text())
        avail = min(avail, cap - current)
    except (OSError, ValueError):
        pass
    swap = int(next(line.split()[1] for line in Path("/proc/meminfo").read_text().splitlines() if line.startswith("SwapTotal:")))
    return avail, swap
avail, swap = reserve()
if avail < 4 * 1024**3 or swap:
    raise SystemExit("resource preflight failed")
child = subprocess.Popen(command, env=env, preexec_fn=prepare)
peak = 0
reason = None
while child.poll() is None:
    rss = 0
    for stat in Path("/proc").glob("[0-9]*/stat"):
        try:
            fields = stat.read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) == child.pid:
                rss += int(fields[21]) * os.sysconf("SC_PAGE_SIZE")
        except (OSError, ValueError, IndexError):
            pass
    peak = max(peak, rss)
    avail, swap = reserve()
    if rss > 12 * 1024**3:
        reason = "aggregate RSS cap"
    elif avail < 4 * 1024**3:
        reason = "available reserve"
    elif swap:
        reason = "swap enabled"
    elif time.monotonic() - started > a.seconds:
        reason = "wall timeout"
    if reason:
        os.killpg(child.pid, signal.SIGKILL)
        break
    time.sleep(0.1)
code = child.wait()
# Any descendants must end with this one-shot gate, including on parent failure.
try:
    os.killpg(child.pid, signal.SIGKILL)
except ProcessLookupError:
    pass
print(json.dumps({"command": command, "exit": code, "stop": reason, "elapsed_seconds": time.monotonic() - started, "sampled_peak_group_rss": peak}), flush=True)
raise SystemExit(1 if reason else code)
