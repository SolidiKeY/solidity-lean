#!/usr/bin/env python3
"""Check that the three V08 census sets partition all original controls."""
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = '4d3790eadb8a5212233bc7d5e345817476b2f590'
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE, '--', 'Solidity/Lowering/V08'], cwd=ROOT, text=True).splitlines()
original = {p.removesuffix('.lean').replace('/', '.') for p in paths if p.endswith('Controls.lean')}
source = set((ROOT / 'tests/h55/shared-fixtures/source-exec-modules.txt').read_text().splitlines())
remaining = set((ROOT / 'tests/h55/shared-fixtures/v08-remaining-modules.txt').read_text().splitlines())
changed = {'Solidity.Lowering.V08.' + name + 'Controls' for name in ('Handler', 'LibraryHandler', 'CreationSuccess', 'Prefix')}
if source & remaining or source & changed or remaining & changed or source | remaining | changed != original:
    raise SystemExit('V08 partition does not match original controls')
if (len(original), len(source), len(remaining), len(changed)) != (106, 74, 28, 4):
    raise SystemExit('unexpected V08 partition counts')
print('original V08 controls=106; execution=74; remaining=28; changed-and-compared=4')
