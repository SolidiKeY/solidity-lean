#!/usr/bin/env python3
"""Measure one command; terminate its process group before losing 4 GiB headroom.

The caller must hold the repository writer lock. Outputs are external evidence.
A resource stop is exit 75, never a passing gate. No swap is permitted.
"""
import argparse
import json
import os
from pathlib import Path
import signal
import resource
import subprocess
import time

GIB = 1024 ** 3
CG = Path('/sys/fs/cgroup')


class SupervisorInterrupted(BaseException):
    """Cancellation must bypass OSError handling in process inspection."""



def resources():
    info = {k: int(v.split()[0]) * 1024 for k, v in
            (line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())}
    maximum = (CG / 'memory.max').read_text().strip()
    current = int((CG / 'memory.current').read_text())
    available = info['MemAvailable']
    if maximum != 'max':
        available = min(available, int(maximum) - current)
    return available, info.get('SwapTotal', 0), current


def group_rss(group):
    total = 0
    for stat in Path('/proc').glob('[0-9]*/stat'):
        try:
            # comm can contain whitespace and parentheses.
            fields = stat.read_text().rsplit(')', 1)[1].split()
            if int(fields[2]) == group:
                total += int(fields[21]) * os.sysconf('SC_PAGE_SIZE')
        except (OSError, ValueError, IndexError):
            continue
    return total


def main():
    p = argparse.ArgumentParser()
    p.add_argument('output', type=Path)
    p.add_argument('command', nargs=argparse.REMAINDER)
    a = p.parse_args()
    if not a.command:
        p.error('missing command')
    if a.output.exists() or a.output.with_suffix('.log').exists():
        p.error('evidence paths already exist; choose a new run name')
    available, swap, current = resources()
    if available < 4 * GIB or swap:
        raise SystemExit('resource prerequisite failed: require 4 GiB available and no swap')
    start = time.monotonic()
    peak = 0
    lowest = available
    stopped = None
    child = None
    code = None
    error = None

    def stop_group(sig):
        if child is not None:
            try:
                os.killpg(child.pid, sig)
            except ProcessLookupError:
                pass

    def interrupted(signum, _frame):
        raise SupervisorInterrupted('supervisor signal '+str(signum))

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        with a.output.with_suffix('.log').open('x') as log:
            child = subprocess.Popen(a.command, stdout=log, stderr=subprocess.STDOUT,
                                     start_new_session=True)
            while child.poll() is None:
                available, swap, current = resources()
                peak = max(peak, group_rss(child.pid))
                lowest = min(lowest, available)
                if available < 4 * GIB or swap:
                    stopped = 'resource-headroom-or-swap'
                    break
                time.sleep(0.2)
            if stopped:
                stop_group(signal.SIGTERM)
                try:
                    child.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    pass
            else:
                code = child.wait()
                if group_rss(child.pid):
                    stopped = 'descendants-after-command-exit'
    except BaseException as exc:
        error = type(exc).__name__ + ': ' + str(exc)
        stopped = 'launcher-or-monitor-error'
    finally:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        stop_group(signal.SIGKILL)
        if child is not None:
            code = child.wait()
    result = dict(command=a.command, cwd=os.getcwd(), exit=75 if stopped else code,
                  child_exit=code, resource_stop=stopped, error=error, wall_seconds=time.monotonic()-start,
                  maximum_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                  sampled_peak_group_rss_bytes=peak, minimum_available_bytes=lowest,
                  sample_interval_seconds=0.2, memory_max=(CG/'memory.max').read_text().strip(),
                  swap_max=(CG/'memory.swap.max').read_text().strip())
    with a.output.open('x') as evidence:
        evidence.write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)
    raise SystemExit(result['exit'])


if __name__ == '__main__':
    main()
