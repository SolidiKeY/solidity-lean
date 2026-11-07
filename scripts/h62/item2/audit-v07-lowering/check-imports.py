#!/usr/bin/env python3
"""Serial bounded compiler check of frozen mapped modules' import closure.
No Lake/old-toolchain cache, no source edits, no generated root registration.
Default stops at first error; --keep-going checks independent import branches.
Successful files alone are not a full acceptance gate.
"""
import argparse
import hashlib
import json
import os
import pathlib
import resource
import subprocess
import time
from census import census, masked

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', required=True, type=pathlib.Path)
p.add_argument('--toolchain', required=True, type=pathlib.Path)
p.add_argument('--evidence', required=True, type=pathlib.Path)
p.add_argument('--keep-going', action='store_true', help='check independent branches and record skipped dependents')
a = p.parse_args()
a.evidence.mkdir(parents=True, exist_ok=True)
output = a.evidence / 'olean'
output.mkdir(exist_ok=True)
seen = set()
order = []
dependencies = {}


def visit(module):
    if module in seen:
        return
    seen.add(module)
    source = a.repo / (module.replace('.', '/')+'.lean')
    if not source.exists():
        if module.startswith(('Lean', 'Init', 'Std', 'Lake')):
            return
        raise RuntimeError(f'unresolved import {module}')
    text = masked(source.read_text())
    dependencies[module] = []
    import re
    for line in text.splitlines():
        m = re.match(r'\s*(?:(?:public|private)\s+)?import\s+(.+)', line)
        if m:
            for dependency in m[1].split():
                dependencies[module].append(dependency)
                visit(dependency)
    order.append((module, source))


for row in census(a.repo)['modules']:
    visit(row['path'][:-5].replace('/', '.'))
(a.evidence / 'import-order.json').write_text(json.dumps([m for m, _ in order], indent=2)+'\n')
env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(output))
results = []
failed = set()


def limit():
    resource.setrlimit(resource.RLIMIT_AS, (12*1024**3, 12*1024**3))


for module, source in order:
    blocked_by = [d for d in dependencies[module] if d in failed]
    if blocked_by:
        failed.add(module)
        results.append(dict(module=module, exit=None, status='skipped-dependency', blocked_by=blocked_by))
        (a.evidence/'results.json').write_text(json.dumps(results, indent=2)+'\n')
        continue
    available = next(int(x.split()[1])*1024 for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
    dest = output / (module.replace('.', '/')+'.olean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    cmd = [str(a.toolchain/'bin/lean'), '-j1', '--tstack=131072', '-o', str(dest), str(source.relative_to(a.repo))]
    started = time.monotonic()
    reason = None
    status = 0
    with (a.evidence/(module+'.log')).open('w') as log:
        if available < 4*1024**3:
            status, reason = 125, 'resource: less than 4 GiB available before launch'
        else:
            proc = subprocess.Popen(cmd, cwd=a.repo, env=env, stdout=log, stderr=subprocess.STDOUT, preexec_fn=limit)
            while proc.poll() is None:
                available = next(int(x.split()[1])*1024 for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
                if available < 4*1024**3 or time.monotonic()-started > 300:
                    reason = 'resource: less than 4 GiB available' if available < 4*1024**3 else 'timeout: 300 seconds'
                    proc.kill()  # Only the process created by this driver.
                    break
                time.sleep(0.1)
            status = proc.wait()
    row = dict(module=module, command=cmd, exit=status, blocker=reason, seconds=round(time.monotonic()-started, 3), source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
    results.append(row)
    (a.evidence/'results.json').write_text(json.dumps(results, indent=2)+'\n')
    print(module, status, row['seconds'], flush=True)
    if status:
        failed.add(module)
        if reason or not a.keep_going:
            raise SystemExit(status)
if failed:
    raise SystemExit(1)
