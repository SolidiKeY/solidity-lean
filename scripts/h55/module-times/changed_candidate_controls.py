#!/usr/bin/env python3
"""Guard regression: changed symbolic-location or witness tooling keeps an obsolete reference."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
ROLES = {
    'tests/h62/item1/evm-lemmas/LocationFixture.lean': {
        'role': 'unregistered symbolic location inequalities and explicit hashed-word alias controls; no concrete hash injectivity',
        'driver': 'historical isolated Lean check documented in docs/feature-work/h62-1-evm-lemmas.md; current invocation unresolved',
        'inputs': 'Solidity.Storage.HashedSeparation and exact current import/toolchain/cache closure',
        'effects': 'no direct file output established; driver may write logs and oleans'},
    'tests/h62/item2/audit-evm-compiler/JointWitness.lean': {
        'role': 'complete dependent-telescope joint-witness tooling; guarded rejections are expected-success controls, not impossible-input witnesses',
        'driver': 'scripts/h62/item2/audit-evm-compiler/Closed.lean imports this tool; exact current driver unresolved',
        'inputs': 'JointImpossible and exact current import/toolchain/cache closure',
        'effects': 'adds checked declarations in elaboration environment; external drivers may write census evidence'},
}


def classify(root, rows):
    if not isinstance(rows, list):
        raise ValueError('invalid drift rows')
    root = Path(root).resolve()
    out, seen = [], set()
    for entry in rows:
        if not isinstance(entry, dict) or not isinstance(entry.get('candidate'), dict):
            raise ValueError('invalid candidate')
        row = entry['candidate']
        path = row.get('path')
        if path not in ROLES:
            continue
        if path in seen or entry.get('state') != 'changed-candidate-review':
            raise ValueError('duplicate or unexpected drift state')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from drift snapshot')
        out.append({'candidate': row, **ROLES[path], 'expected_outcome': 'current execution unresolved',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: changed_candidate_controls.py DRIFT.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'drift-subset-only-unverified',
                          'input_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, data['rows'])}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'changed candidate classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
