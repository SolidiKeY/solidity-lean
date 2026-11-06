#!/usr/bin/env python3
"""Run only this lane's process tree with a 12 GiB RSS cap / 4 GiB reserve.

No systemd or swap setup. Report resource stops as failures. Child stdin/stdout
are inherited, permitting a guarded stdio MCP server. This does not alter Lean
proof budgets or supply proof evidence by itself.
"""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import time

GIB = 1024**3


def process_table():
    rows = {}
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit(): continue
        try:
            stat = (entry/'stat').read_text().rsplit(')', 1)[1].split()
            rows[int(entry.name)] = dict(parent=int(stat[1]), session=int(stat[3]),
                rss=int(stat[21])*os.sysconf('SC_PAGE_SIZE'), started=int(stat[19]), state=stat[0])
        except (OSError, ValueError, IndexError): pass
    return rows


def process_tree(root, known):
    rows = process_table()
    owned = {pid for pid, row in rows.items() if row['session'] == root or
             (pid in known and row['started'] == known[pid])}
    while True:
        more = {pid for pid, row in rows.items() if row['parent'] in owned}
        if more <= owned: break
        owned |= more
    identities = {pid: rows[pid]['started'] for pid in owned}
    live = {pid for pid in owned if rows[pid]['state'] != 'Z'}
    return identities, live, sum(rows[pid]['rss'] for pid in owned)


def signal_owned(identities, signum):
    for pid, started in identities.items():
        current = process_table().get(pid)
        if current is not None and current['started'] == started:
            try: os.kill(pid, signum)
            except ProcessLookupError: pass


def available():
    mem = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
    host = int(mem['MemAvailable'].split()[0])*1024
    cg = Path('/sys/fs/cgroup')
    maximum = (cg/'memory.max').read_text().strip()
    if maximum == 'max': return host
    current = int((cg/'memory.current').read_text())
    stats = dict(line.split() for line in (cg/'memory.stat').read_text().splitlines())
    reclaimable = int(stats.get('inactive_file', 0))
    return min(host, int(maximum)-max(0, current-reclaimable))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True, type=Path)
    parser.add_argument('--timeout', type=float, default=28800)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command: parser.error('missing command')
    if available() < 4*GIB: raise SystemExit('resource reserve unavailable before launch')
    if 'SwapTotal:             0 kB' not in Path('/proc/meminfo').read_text():
        swap = next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('SwapTotal:'))
        if int(swap) != 0: raise SystemExit('no-swap prerequisite unavailable')
    start = time.monotonic()
    peak, minimum, stop = 0, available(), None
    termination_signal = None
    known = {}
    def terminate(signum, _frame):
        nonlocal termination_signal
        termination_signal = signum
        raise SystemExit(128+signum)
    signal.signal(signal.SIGTERM, terminate)
    child = subprocess.Popen(command, start_new_session=True)
    try:
        while True:
            known, live, rss = process_tree(child.pid, known)
            free = available()
            peak, minimum = max(peak, rss), min(minimum, free)
            if child.poll() is not None:
                if live - {child.pid}: stop = 'launcher exited with live child processes'
                break
            if rss > 12*GIB: stop = 'aggregate RSS exceeded 12 GiB'
            elif free < 4*GIB: stop = 'available reserve fell below 4 GiB'
            elif time.monotonic()-start > args.timeout: stop = 'wall timeout'
            if stop: break
            time.sleep(0.25)
    finally:
        known, live, _ = process_tree(child.pid, known)
        if live:
            signal_owned(known, signal.SIGTERM)
            deadline = time.monotonic()+5
            while live and time.monotonic() < deadline:
                child.poll()
                known, live, _ = process_tree(child.pid, known)
                if live: time.sleep(0.1)
            if live: signal_owned(known, signal.SIGKILL)
        child.wait()
        args.report.write_text(json.dumps(dict(command=command, exit_code=child.returncode,
            seconds=time.monotonic()-start, peak_tree_rss_bytes=peak,
            minimum_available_bytes=minimum, resource_stop=stop,
            termination_signal=termination_signal), indent=2)+'\n')
    raise SystemExit(75 if stop else child.returncode)


if __name__ == '__main__': main()
