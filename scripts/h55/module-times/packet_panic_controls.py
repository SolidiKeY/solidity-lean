#!/usr/bin/env python3
"""Guard regression: isolated panic-byte fixtures imply target payload correctness."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item1/packet-panic/'
ROLES = {
    'CheckedMulEquivalence': 'candidate proof-term equalities to unchanged checked multiplication controls; not selected target payload',
    'CheckedSubEquivalence': 'candidate proof-term equalities to unchanged checked subtraction controls; not selected target payload',
    'PanicBytes': 'candidate shared Source arithmetic-panic observations; no selected target payload property',
    'PanicBytesFixture': 'isolated list fixture; not linked to Source.panicData or target execution',
}


def classify(root, rows):
    if not isinstance(rows, list):
        raise ValueError('invalid coverage rows')
    root = Path(root).resolve()
    out, seen = [], set()
    for entry in rows:
        if not isinstance(entry, dict) or not isinstance(entry.get('candidate'), dict):
            raise ValueError('invalid candidate')
        row = entry['candidate']
        path = row.get('path')
        if not isinstance(path, str) or not path.startswith(PREFIX):
            continue
        filename = path[len(PREFIX):]
        if not filename.endswith('.lean') or filename[:-5] not in ROLES or path in seen or entry.get('status') != 'no-supplied-per-path-reference':
            raise ValueError('unreviewed, duplicate or unexpected candidate')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from coverage snapshot')
        out.append({'candidate': row, 'role': ROLES[filename[:-5]],
                    'driver': 'historical packet-panic isolated serial/MCP diagnostics are candidate references; exact current per-file invocation unresolved',
                    'inputs': 'source/import closure, isolated Lean 4.35 toolchain and cache; current inputs unverified',
                    'effects': 'no direct file output established; candidate tooling writes isolated cache, logs and receipts',
                    'expected_outcome': 'current execution unresolved; historical dependency closure failed and is not to be rerun unchanged',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: packet_panic_controls.py COVERAGE.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'supplied-snapshot-subset-only-unverified',
                          'input_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, data['rows'])}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'packet panic classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
