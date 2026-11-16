#!/usr/bin/env python3
"""Select pinned StorageOps control modules declaring a lexical fitting helper."""
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = '4d3790eadb8a5212233bc7d5e345817476b2f590'
AREAS = ('Solidity/Backend/StorageOps', 'Solidity/Lowering/StorageOps')
DECL = re.compile(rb'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:def|theorem|lemma)\s+fitting\b', re.M)
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE, '--', *AREAS], cwd=ROOT, text=True).splitlines()
for name in sorted(p for p in paths if p.endswith('Controls.lean')):
    original = subprocess.check_output(['git', 'show', f'{BASE}:{name}'], cwd=ROOT)
    if not DECL.search(original):
        continue
    if (ROOT / name).read_bytes() != original:
        raise SystemExit(f'changed source requires explicit comparison: {name}')
    print(name.removesuffix('.lean').replace('/', '.'))
