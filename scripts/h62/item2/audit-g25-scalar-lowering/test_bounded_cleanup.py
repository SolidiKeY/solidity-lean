#!/usr/bin/env python3
"""Regression: resource cleanup must immediately kill/reap TERM-resistant detached children.
This tiny process fixture does not reproduce the OOM or change any guard threshold.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time


def fixture_cleanup(proc):
    # Independent of the cleanup method under test: reap our own sessions even
    # if setup or that method raises. This fixture is single-job/subreaper.
    for _ in range(2):
        records = {}
        for entry in Path('/proc').iterdir():
            if not entry.name.isdigit(): continue
            try:
                raw = (entry/'stat').read_text()
                fields = raw[raw.rfind(')')+2:].split()
                records[int(entry.name)] = (int(fields[1]),fields[19])
            except (OSError,ValueError): pass
        owned = {proc.pid} | {pid for pid,(parent,_) in records.items() if parent == os.getpid()}
        while True:
            more = {pid for pid,(parent,_) in records.items() if parent in owned}
            if more <= owned: break
            owned |= more
        for pid in owned:
            if pid not in records: continue
            try:
                raw = Path('/proc',str(pid),'stat').read_text()
                current = raw[raw.rfind(')')+2:].split()[19]
                if current == records[pid][1]: os.kill(pid,9)
            except (OSError,ValueError): pass
        proc.wait()
        for pid in owned:
            if pid == proc.pid: continue
            try: os.waitpid(pid,0)
            except ChildProcessError: pass
    remaining = []
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit(): continue
        try:
            raw = (entry/'stat').read_text()
            if int(raw[raw.rfind(')')+2:].split()[1]) == os.getpid(): remaining.append(int(entry.name))
        except (OSError,ValueError): pass
    print(json.dumps({'fixture_final_cleanup_remaining':remaining}))
    if remaining: raise RuntimeError('fixture cleanup left owned children')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--legacy', type=Path)
    parser.add_argument('--simulate-cleanup-error', action='store_true')
    args = parser.parse_args()
    module_path = args.legacy or Path(__file__).with_name('bounded_lean.py')
    spec = importlib.util.spec_from_file_location('cleanup_runner', module_path)
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)
    runner.subreaper()
    grandchild = "import signal,time;from pathlib import Path;import sys;signal.signal(signal.SIGTERM,signal.SIG_IGN);Path(sys.argv[1]).write_text('ready');time.sleep(60)"
    child = """import signal,subprocess,sys,time
from pathlib import Path
signal.signal(signal.SIGTERM,signal.SIG_IGN)
p=subprocess.Popen([sys.executable,'-c',sys.argv[1],sys.argv[2]],start_new_session=True)
while not Path(sys.argv[2]).exists():time.sleep(.01)
Path(sys.argv[3]).write_text(str(p.pid))
time.sleep(60)
"""
    with tempfile.TemporaryDirectory(prefix='bounded-cleanup-') as directory:
        ready, pidfile = Path(directory)/'ready', Path(directory)/'pid'
        proc = subprocess.Popen([sys.executable,'-c',child,grandchild,str(ready),str(pidfile)],start_new_session=True)
        try:
            deadline = time.monotonic()+5
            while not pidfile.exists():
                if proc.poll() is not None or time.monotonic()>deadline:
                    raise RuntimeError('fixture failed to start')
                time.sleep(.01)
            detached = int(pidfile.read_text())
            start = time.monotonic()
            if args.simulate_cleanup_error:
                raise RuntimeError('intentional fixture failure before tested cleanup')
            if args.legacy:
                runner.terminate(proc)
            else:
                runner.terminate(proc, force=True)
            elapsed = time.monotonic()-start
            remaining = [pid for pid in (proc.pid,detached) if Path('/proc',str(pid)).exists()]
            report = {'legacy':bool(args.legacy),'seconds':elapsed,'exit':proc.returncode,
                      'remaining_owned_pids':remaining,'threshold_seconds':2,
                      'boundary':'cleanup fixture only; no Lean/OOM or resource-budget increase'}
            print(json.dumps(report))
            if remaining or elapsed>=2:
                raise SystemExit(1)
        finally:
            fixture_cleanup(proc)


if __name__ == '__main__':
    main()
