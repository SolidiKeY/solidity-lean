#!/usr/bin/env python3
"""Select unchanged original backend controls outside the fitting candidate set."""
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = '4d3790eadb8a5212233bc7d5e345817476b2f590'
AREA = 'Solidity/Backend/StorageOps'
fitting = set((ROOT / 'tests/h55/shared-fixtures/fitting-modules.txt').read_text().splitlines())
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE, '--', AREA], cwd=ROOT, text=True).splitlines()
for name in sorted(p for p in paths if p.endswith('Controls.lean')):
    module = name.removesuffix('.lean').replace('/', '.')
    if module in fitting:
        continue
    original = subprocess.check_output(['git', 'show', f'{BASE}:{name}'], cwd=ROOT)
    if (ROOT / name).read_bytes() != original:
        raise SystemExit(f'changed source requires explicit comparison: {name}')
    print(module)
