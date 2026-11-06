#!/usr/bin/env python3
"""Deterministic external acceptance; never substitutes for Lean proofs/gates."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
from census import census, sha, FAMILY
from audit import audit

def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + '\n').encode()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--base', default='c6f550e281a7e5affa9a99bc2cdaed556dec00e4')
    p.add_argument('--root', type=Path, default=Path.cwd())
    p.add_argument('--frozen', type=Path, required=True)
    p.add_argument('--audit', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    inventory = encoded(census(a.root))
    repeated = encoded(census(a.root))
    if inventory != repeated or inventory != a.frozen.read_bytes():
        raise SystemExit('ACCEPT_FAIL: nondeterminism or frozen family changed')
    rows = json.loads(inventory)['files']
    paths = subprocess.check_output(['git', 'ls-tree', '-rz', '--name-only', a.base, '--', str(FAMILY)], cwd=a.root).decode().split('\0')
    originals = sorted(path for path in paths if path.endswith('.lean'))
    if originals != [row['path'] for row in rows]:
        raise SystemExit('ACCEPT_FAIL: family file inventory differs from published base')
    refs = ''.join(a.base + ':' + row['path'] + '\n' for row in rows).encode()
    batch = subprocess.run(['git', 'cat-file', '--batch'], input=refs, capture_output=True, cwd=a.root, check=True).stdout
    offset = 0
    for row in rows:
        end = batch.index(b'\n', offset)
        fields = batch[offset:end].split()
        if len(fields) != 3 or fields[1] != b'blob':
            raise SystemExit('ACCEPT_FAIL: missing published source blob')
        size = int(fields[2])
        data = batch[end + 1:end + 1 + size]
        if sha(data) != row['sha256']:
            raise SystemExit('ACCEPT_FAIL: family source differs from exact base: ' + row['path'])
        offset = end + size + 2
    report = encoded(audit(json.loads(inventory)))
    if report != a.audit.read_bytes():
        raise SystemExit('ACCEPT_FAIL: audit candidates changed')
    test = a.root / 'tests/h62/item4/generic-memorycopies/test_census.py'
    checked = subprocess.run([sys.executable, '-B', str(test)], capture_output=True, text=True)
    if checked.returncode:
        raise SystemExit(checked.stdout + checked.stderr)
    result = dict(status='EXTERNAL_ACCEPT_PASS', base=a.base, base_files_verified=len(rows), inventory_sha256=sha(inventory), audit_sha256=sha(report),
                  parser_test_exit=checked.returncode, parser_test_output=checked.stderr,
                  proof_boundary='No semantic proof, compile gate, axiom audit or before/after speed acceptance implied.')
    a.output.write_bytes(encoded(result))
    print(json.dumps(result, sort_keys=True))

if __name__ == '__main__':
    main()
