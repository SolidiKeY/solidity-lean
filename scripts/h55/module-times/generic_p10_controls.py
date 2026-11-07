#!/usr/bin/env python3
"""Guard regression: diagnostic transport success masks failed generic P10 guards."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item4/generic-p10/'
ROLES = {
    'GenericP10.lean': 'package root imports fixture, controls, correspondence and local axiom audit',
    'GenericP10/ByteFixture.lean': 'parameterized BYTE execution under byte-algebra observation premise and finite fixture table',
    'GenericP10/ByteControls.lean': 'candidate byte controls preserve original declaration signatures',
    'GenericP10/Correspondence.lean': 'equalities of original and candidate propositions; not proof identity',
    'GenericP10/AxiomAudit.lean': 'local guarded headline axiom pins, not the central complete axiom audit',
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
                    'driver': 'separate Lake package and accept_semantics.py requires Lean MCP; current invocation unresolved',
                    'inputs': 'package Lean 4.24 pin, Bridge dependency, toolchain and cache; current bytes and availability unverified',
                    'effects': 'acceptance may start Lean MCP and write off-git evidence; generators can overwrite candidate files',
                    'expected_outcome': 'diagnostic transport exit alone does not prove guard success; production Bridge gate and current result unresolved',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: generic_p10_controls.py CENSUS.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'unverified-subsets-accepted',
                          'census_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError) as exc:
        print(f'generic P10 classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
