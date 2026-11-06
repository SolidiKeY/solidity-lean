#!/usr/bin/env python3
"""Fresh serial source builds into an isolated v4.35 object directory.

Each module is bounded independently via bounded.py. Never consult .lake or
v4.24 artifacts; originals are inputs only. No budget/option/source rewrites.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from census import mask

REPO = Path(__file__).resolve().parents[4]
RUNTIME = Path('/workspace/h62-runtime')
LEAN = RUNTIME / 'toolchains/lean-4.35.0-linux/bin/lean'

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('modules', nargs='+')
    args = ap.parse_args()
    obj = RUNTIME / 'objects'
    logs = RUNTIME / 'evidence' / ('closure-' + '-'.join(args.modules))
    obj.mkdir(exist_ok=True)
    logs.mkdir(exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(obj), LEAN_NUM_THREADS='1')
    visited = set()
    order = []
    def visit(module):
        if module in visited or module.startswith(('Lean.', 'Std.')) or module in ('Lean', 'Std'):
            return
        visited.add(module)
        path = REPO / (module.replace('.', '/') + '.lean')
        if not path.is_file():
            raise SystemExit('MISSING_SOURCE ' + str(path))
        for name in re.findall(r'(?m)^import ([^ \n]+)', mask(path.read_text())):
            visit(name.replace('«', '').replace('»', ''))
        order.append((module, path))
    for module in args.modules:
        visit(module)
    records = []
    for module, path in order:
        out = obj / (module.replace('.', '/') + '.olean')
        out.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (module + '.log')
        # Deliberately fresh; unchanged prerequisites may be rebuilt in a new run.
        command = [sys.executable, str(Path(__file__).with_name('bounded.py')),
                   '--log', str(log), '--', str(LEAN), '-j1', '--tstack=131072',
                   '-o', str(out), str(path)]
        print('BUILD ' + module, flush=True)
        result = subprocess.run(command, cwd=REPO, env=env)
        records.append(dict(module=module, source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(), exit=result.returncode))
        (logs / 'index.json').write_text(json.dumps(records, indent=2)+'\n')
        if result.returncode:
            print(log.read_text()[-6000:])
            raise SystemExit(result.returncode)

if __name__ == '__main__':
    main()
