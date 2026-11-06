#!/usr/bin/env python3
"""Reproduce the frozen source census. Does not run or certify Lean proofs."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import census

BRANCH = 'codex/solidity-h62-4-20261106/generic-p10'


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args])


def verify(repo, inventory_path, receipt_path):
    receipt = json.loads(receipt_path.read_text())
    raw = inventory_path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != receipt['inventory_sha256']:
        raise ValueError('inventory checksum differs from committed receipt')
    expected = json.loads(raw)
    if expected['base'] != census.BASE or receipt['base'] != census.BASE:
        raise ValueError('wrong base')
    if git(repo, 'branch', '--show-current').decode().strip() != BRANCH:
        raise ValueError('wrong branch')
    subprocess.run(['git', '-C', str(repo), 'merge-base', '--is-ancestor', census.BASE, 'HEAD'], check=True)
    frozen_paths = git(repo, 'ls-tree', '-r', '--name-only', census.BASE, '--', str(census.FAMILY)).decode().splitlines()
    frozen_paths = sorted(p for p in frozen_paths if p.endswith('.lean'))
    if frozen_paths != [f['path'] for f in expected['files']]:
        raise ValueError('inventory differs from the full pinned family file set')
    for source in expected['files']:
        frozen = git(repo, 'show', f"{census.BASE}:{source['path']}")
        if hashlib.sha256(frozen).hexdigest() != source['source_sha256']:
            raise ValueError(f"inventory has unpinned source: {source['path']}")
    actual = census.render(census.census(repo)).encode()
    if actual != raw: raise ValueError('current source census differs from frozen inventory')
    if expected['summary'] != receipt['summary']: raise ValueError('receipt summary differs')
    changed = git(repo, 'diff', '--name-only', census.BASE, '--').decode().splitlines()
    changed += git(repo, 'diff', '--cached', '--name-only', census.BASE, '--').decode().splitlines()
    changed += git(repo, 'ls-files', '--others', '--exclude-standard').decode().splitlines()
    for path in changed:
        if not (path.startswith('tests/h62/item4/generic-p10/') or
                path.startswith('scripts/h62/item4/generic-p10/') or
                path == 'docs/feature-work/h62-4-generic-p10.md'):
            raise ValueError(f'write scope violation: {path}')
        if '__pycache__' in path or path.endswith('.pyc'): raise ValueError(f'transient file: {path}')
    print(f"SOURCE_ACCEPTANCE_PASS: {len(frozen_paths)} pinned files; exact inventory and write scope")
    print('BOUNDARY: no Lean elaboration, semantic correspondence, runtime gate or performance acceptance claimed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--inventory', type=Path, required=True)
    args = parser.parse_args()
    receipt = args.repo/'tests/h62/item4/generic-p10/census-receipt.json'
    tests = args.repo/'tests/h62/item4/generic-p10/test_census.py'
    subprocess.run([sys.executable, '-B', str(tests), '-v'], check=True)
    verify(args.repo, args.inventory, receipt)


if __name__ == '__main__': main()
