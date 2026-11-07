#!/usr/bin/env python3
"""Guard regression: conditional transport or compatibility is mistaken for a completed migration."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h55/source-relations/'
ROLES = {
    'ContextMapAcceptance': 'generic full-contract transport assumes universal pointwise equivalence; no concrete producer or simulation',
    'HelperCompatibility': 'typed owner compatibility inventory against existing producers; no helper migration or Lean 4.35 acceptance',
    'InferAcceptance': 'existing helper and inferencer obligations; successful Option type membership does not assert chosen derivation identity',
    'RelationRoundtrip': 'roundtrips for existing primitive and locals relations; no new world correspondence or execution simulation',
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
        if not name.endswith('.lean') or name[:-5] not in ROLES or path in seen:
            raise ValueError('unreviewed or duplicate candidate')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from census')
        name = name[:-5]
        out.append({'candidate': row, 'role': ROLES[name],
                    'driver': 'historical standalone Lean checks and scripts/h55/source-relations/bounded.py; default 600s is not the 300s gate; current invocation unresolved',
                    'inputs': 'imported source and olean closure, toolchain and cache; current identities unverified',
                    'effects': 'bounded runner may write isolated evidence and use Docker; exact invocation unverified',
                    'expected_outcome': 'historical proof reports are not current gate acceptance',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: source_relation_controls.py CENSUS.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'unverified-subsets-accepted',
                          'census_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError) as exc:
        print(f'source relation classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
