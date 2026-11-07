#!/usr/bin/env python3
"""Serial subprocess runner with a hard address-space bound and headroom guard.

No swap exists on this VM. This does not claim RLIMIT_AS is a cgroup RSS bound.
The inherited cgroup cap applies in addition. Logs/metrics are external artifacts.
"""
import argparse
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

GIB = 1024**3

def available():
    host = int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines()
                    if l.startswith('MemAvailable:'))) * 1024
    cap = Path('/sys/fs/cgroup/memory.max').read_text().strip()
    if cap != 'max':
        host = min(host, int(cap) - int(Path('/sys/fs/cgroup/memory.current').read_text()))
    return host


def run(argv, log, timeout=900):
    if available() < 4 * GIB: raise RuntimeError('less than 4 GiB reserve before launch')
    started = time.monotonic()
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (12 * GIB, 12 * GIB))
    with open(log, 'w') as out:
        proc = subprocess.Popen(argv, stdout=out, stderr=subprocess.STDOUT,
                                start_new_session=True, preexec_fn=limits)
        reason = None
        peak = 0
        peak_virtual = 0
        peak_threads = 0
        while proc.poll() is None:
            if available() < 4 * GIB: reason = 'headroom-stop'
            elif time.monotonic() - started > timeout: reason = 'timeout'
            try:
                status = Path(f'/proc/{proc.pid}/status').read_text()
                rss = next((int(l.split()[1]) * 1024 for l in status.splitlines() if l.startswith('VmRSS:')), 0)
                peak = max(peak, rss)
                virtual = next((int(l.split()[1]) * 1024 for l in status.splitlines() if l.startswith('VmSize:')), 0)
                threads = next((int(l.split()[1]) for l in status.splitlines() if l.startswith('Threads:')), 0)
                peak_virtual = max(peak_virtual, virtual)
                peak_threads = max(peak_threads, threads)
            except FileNotFoundError: pass
            if reason:
                os.killpg(proc.pid, signal.SIGTERM)
                try: proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                break
            time.sleep(0.1)
    return {'command': argv, 'exit': proc.returncode, 'wall_seconds': time.monotonic()-started,
            'peak_sampled_rss_bytes': peak, 'peak_sampled_virtual_bytes': peak_virtual,
            'peak_sampled_threads': peak_threads, 'stop_reason': reason, 'log': str(log)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--log', type=Path, required=True)
    ap.add_argument('--metrics', type=Path, required=True)
    ap.add_argument('--timeout', type=int, default=900)
    ap.add_argument('command', nargs=argparse.REMAINDER)
    a = ap.parse_args()
    cmd = a.command[1:] if a.command[0] == '--' else a.command
    result = run(cmd, a.log, a.timeout)
    a.metrics.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))
    raise SystemExit(result['exit'] or (1 if result['stop_reason'] else 0))

if __name__ == '__main__': main()
