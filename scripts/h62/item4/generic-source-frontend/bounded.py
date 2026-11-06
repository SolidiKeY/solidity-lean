#!/usr/bin/env python3
"""Serial bounded subprocess runner. No systemd, swap, or foreign PID kills.

12 GiB hard virtual-memory cap (stronger than RSS cap), 4 GiB available
reserve, own process-group timeout; caller supplies explicit Lean -j1.
"""
import argparse
import fcntl
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

GIB = 1024 ** 3

def effective_available(mem, cgroup_root=Path('/sys/fs/cgroup')):
    host = int(mem['MemAvailable'].split()[0]) * 1024
    cap = (cgroup_root/'memory.max').read_text().strip()
    charged = int((cgroup_root/'memory.current').read_text().strip())
    remaining = host if cap == 'max' else max(0, int(cap)-charged)
    return min(host, remaining), host, remaining


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--timeout', type=int, default=300)
    ap.add_argument('--log', type=Path, required=True)
    ap.add_argument('command', nargs=argparse.REMAINDER)
    args = ap.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        ap.error('missing command')
    mem = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
    if int(mem['SwapTotal'].split()[0]):
        raise SystemExit('RESOURCE_BLOCKED: swap must be disabled')
    available, host_available, cgroup_available = effective_available(mem)
    if available < 4 * GIB:
        raise SystemExit('RESOURCE_BLOCKED: 4GiB reserve unavailable')
    lock = open('/tmp/solidity-lean-feature-groups-20261025/writer.lock', 'a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (12 * GIB, 12 * GIB))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    started = time.monotonic()
    stopped = None
    peak_rss = 0
    min_available = available
    min_host_available = host_available
    min_cgroup_available = cgroup_available
    with args.log.open('w') as log:
        p = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT,
                             env=env, preexec_fn=limits, start_new_session=True)
        while p.poll() is None:
            mem = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
            available, host_available, cgroup_available = effective_available(mem)
            min_host_available = min(min_host_available, host_available)
            min_cgroup_available = min(min_cgroup_available, cgroup_available)
            min_available = min(min_available, available)
            group_rss = 0
            for stat in Path('/proc').glob('[0-9]*/stat'):
                try:
                    fields = stat.read_text().rsplit(')', 1)[1].split()
                    if int(fields[2]) == p.pid:
                        group_rss += int(fields[21]) * os.sysconf('SC_PAGE_SIZE')
                except (OSError, ValueError, IndexError):
                    pass
            peak_rss = max(peak_rss, group_rss)
            if time.monotonic() - started > args.timeout:
                stopped = 'TIMEOUT'
            elif available < 4 * GIB:
                stopped = 'RESOURCE_RESERVE'
            if stopped:
                os.killpg(p.pid, signal.SIGTERM)
                try:
                    p.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(p.pid, signal.SIGKILL)
                break
            time.sleep(0.1)
        code = p.wait()
    result = dict(command=command, cwd=os.getcwd(), exit=code,
                  outcome=stopped or ('pass' if code == 0 else 'fail'),
                  elapsed_seconds=round(time.monotonic()-started, 6),
                  memory_cap='RLIMIT_AS=12GiB', reserve='min(host MemAvailable,cgroup remaining)>=4GiB',
                  swap_total_kib=int(mem['SwapTotal'].split()[0]), threads=1,
                  sampled_peak_group_rss_bytes=peak_rss, min_available_bytes=min_available,
                  min_host_available_bytes=min_host_available,
                  min_cgroup_available_bytes=min_cgroup_available)
    Path(str(args.log)+'.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))
    raise SystemExit(124 if stopped else code)

if __name__ == '__main__':
    main()
