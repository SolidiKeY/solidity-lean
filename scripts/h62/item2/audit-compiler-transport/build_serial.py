#!/usr/bin/env python3
"""Fresh, serial per-file Lean diagnostics in an external artifact directory.

Does not replace run-lean.sh final gate. Does not reuse Lake artifacts. Requires
caller to hold writer.lock for the entire invocation. No new heartbeat options.
"""
import argparse
import json
import os
from pathlib import Path
import re
import sys
import subprocess
import hashlib
from bounded import run
from census import BASE, mask

ap = argparse.ArgumentParser()
ap.add_argument('--evidence', type=Path, required=True)
ap.add_argument('--lean', type=Path, required=True)
ap.add_argument('--resume', action='store_true')
ap.add_argument('--root', type=Path, default=Path.cwd())
a = ap.parse_args()
a.root = a.root.resolve()
a.evidence = a.evidence.resolve()
output = a.evidence / 'olean'
logs = a.evidence / 'modules'
output.mkdir(exist_ok=True)
logs.mkdir(exist_ok=True)
os.environ['LEAN_PATH'] = str(output)
os.environ['LEAN_NUM_THREADS'] = '1'
mods = re.findall(r'(?m)^\| `([^`]+\.lean)` \|', (a.root/'docs/module-map/compiler-transport.md').read_text())
order, visiting, visited = [], set(), set()

def visit(m):
    if m in visiting: raise ValueError(f'import cycle: {m}')
    if m in visited: return
    p = a.root / (m.replace('.', '/') + '.lean')
    if not p.exists():
        if not m.startswith(('Lean', 'Std', 'Init')): raise ValueError(f'unknown import: {m}')
        return
    visiting.add(m)
    for imp in re.findall(r'^import\s+([^\n]+)', mask(p.read_text()), re.M):
        for dep in imp.split(): visit(dep)
    visiting.remove(m)
    visited.add(m)
    order.append(m)

for m in mods: visit('Solidity.'+m[:-5].replace('/', '.'))
(a.evidence/'build-order.json').write_text(json.dumps(order, indent=2)+'\n')
print(f'Fresh serial dependency closure: {len(order)} local modules', flush=True)
prefix = []
if a.resume:
    prefix = [json.loads(line) for line in (a.evidence/'build-metrics.jsonl').read_text().splitlines()]
    for i, row in enumerate(prefix):
        assert row['exit'] == 0 and not row['stop_reason'] and row['module'] == order[i]
        relative = row['module'].replace('.', '/')+'.lean'
        source = a.root/relative
        frozen = subprocess.check_output(['git','show',f'{BASE}:{relative}'],cwd=a.root)
        assert frozen == source.read_bytes(), f'changed resume source: {relative}'
        artifact = output/(row['module'].replace('.', '/')+'.olean')
        assert artifact.exists(), f'missing owned fresh artifact: {artifact}'
        row['resume_source_sha256'] = hashlib.sha256(frozen).hexdigest()
        row['resume_olean_sha256'] = hashlib.sha256(artifact.read_bytes()).hexdigest()
    (a.evidence/'build-resume-prefix.json').write_text(json.dumps(prefix,indent=2)+'\n')
    print(f'Verified {len(prefix)} owned fresh artifacts/source hashes; resume with serial elaboration',flush=True)
with (a.evidence/'build-metrics.jsonl').open('a' if a.resume else 'w') as metrics:
    for i, m in enumerate(order):
        if i < len(prefix): continue
        source = a.root/(m.replace('.', '/')+'.lean')
        target = output/(m.replace('.', '/')+'.olean')
        target.parent.mkdir(exist_ok=True, parents=True)
        command = [str(a.lean), '-j1', '-DElab.async=false', '--tstack=131072', '-o', str(target), str(source.relative_to(a.root))]
        result = run(command, logs/(m+'.log'))
        result.update(module=m, index=i+1, total=len(order))
        metrics.write(json.dumps(result)+'\n'); metrics.flush()
        print(f'{i+1}/{len(order)} {m}: exit={result["exit"]} {result["wall_seconds"]:.2f}s', flush=True)
        if result['exit'] or result['stop_reason']:
            print('STOP: required module failed; dependent proofs remain unchecked', flush=True)
            sys.exit(result['exit'] or 1)
