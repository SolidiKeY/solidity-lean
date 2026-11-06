#!/usr/bin/env python3
"""Select pinned V08 controls containing lexical execS/evalE references.

This is a bounded candidate set, not a complete semantic scope. Refuses to
scan modified source against the original base.
"""
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = '4d3790eadb8a5212233bc7d5e345817476b2f590'
AREA = 'Solidity/Lowering/V08'
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE, '--', AREA], cwd=ROOT, text=True).splitlines()
for name in sorted(p for p in paths if p.endswith('Controls.lean')):
    original = subprocess.check_output(['git', 'show', f'{BASE}:{name}'], cwd=ROOT)
    if b'execS' not in original and b'evalE' not in original:
        continue
    if (ROOT / name).read_bytes() != original:
        raise SystemExit(f'changed source requires explicit comparison: {name}')
    print(name.removesuffix('.lean').replace('/', '.'))
