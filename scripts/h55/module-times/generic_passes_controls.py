#!/usr/bin/env python3
"""Guard regression: lexical generic-pass aliases become accepted proof or timing results."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item4/generic-passes/'
ROLES = {
    'Generic.lean': 'candidate intrinsic prefix/value composition; operator-specific source transport remains with producer',
    'Fixtures.lean': 'typed original program, machine and observation fixtures; table does not prove arithmetic',
    'Instances.lean': 'candidate execution instances retain full original signatures and producer transport',
    'Correspondence.lean': 'exact-type aliases for original controls; lexical checks do not establish elaborated equivalence',
}


def classify(root, manifest):
    if not isinstance(manifest, dict) or not isinstance(manifest.get('rows'), list):
        raise ValueError('invalid census')
    root = Path(root).resolve()
    out, seen = [], set()
    for row in manifest['rows']:
        if not isinstance(row, dict) or not isinstance(row.get('path'), str):
            raise ValueError('invalid candidate')
        path = row['path']
        if not path.startswith(PREFIX):
            continue
        name = path[len(PREFIX):]
        if name not in ROLES or path in seen:
            raise ValueError('unreviewed or duplicate candidate')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from census')
        out.append({'candidate': row, 'role': ROLES[name],
                    'driver': 'scripts/h62/item4/generic-passes/accept.py and bounded.py; bounded loop has no explicit wall deadline; applicability unresolved',
                    'inputs': 'v4.35 toolchain, transitive source and olean closure, cache and producer controls; current bytes unverified',
                    'effects': 'candidate acceptance and measurement write off-git build, logs and reports',
                    'expected_outcome': 'historical lexical acceptance and plan are not Lean validation; current proof and timing unresolved',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: generic_passes_controls.py CENSUS.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'unverified-subsets-accepted',
                          'census_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError) as exc:
        print(f'generic passes classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
