#!/usr/bin/env python3
"""Guard regression: feasible premise domains imply original bytecode conclusions."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item2/audit-bytecode-selection/'
ROLES = {
    'HypothesisDomains': 'dependent hypothesis-domain feasibility with conclusion replaced by True; not proof of original conclusion',
    'LiteralSuccess': 'supported literal and intrinsic IR success; no external decoder, gas or fork adequacy',
    'RuntimePremiseWitness': 'selected joint runtime inputs use local self-adapter, not external Bridge agreement or general G49',
    'ValueGateSuccess': 'supported intrinsic value-gate observations, not source/native or gas/fork adequacy',
    'Witnesses': 'selected feasibility witnesses plus intentional reject-push impossibility; not a G49 instance',
}


def classify(root, rows):
    if not isinstance(rows, list):
        raise ValueError('invalid reference index')
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
        if not filename.endswith('.lean') or filename[:-5] not in ROLES or path in seen or entry.get('status') != 'no-supplied-current-reference':
            raise ValueError('unreviewed, duplicate or unexpected candidate')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from reference snapshot')
        out.append({'candidate': row, 'role': ROLES[filename[:-5]],
                    'driver': 'scripts/h62/item2/audit-bytecode-selection/verify.py lists all five default roots; current invocation unresolved',
                    'inputs': 'fresh private Lean import closure and frozen Solidity inputs; exact current toolchain and inputs unverified',
                    'effects': 'no direct file output established; verifier writes private oleans, logs and verification JSON',
                    'expected_outcome': 'guarded negative diagnostics require success; current execution and production runner attestation unresolved',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: bytecode_selection_controls.py REFERENCE_INDEX.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'supplied-snapshot-subset-only-unverified',
                          'input_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, data['rows'])}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'bytecode selection classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
