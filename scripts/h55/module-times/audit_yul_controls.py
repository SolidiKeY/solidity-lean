#!/usr/bin/env python3
"""Guard regression: an intentional contradiction is counted as a joint witness."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item2/audit-yul/'
ROLES = {
    'DefaultWitnessControls': 'joint-default controls include an intentionally uncovered empty-context attempt',
    'DefaultWitnesses': 'kernel-checked joint witness construction; failed construction stays uncovered',
    'ImpossiblePremises': 'intentional impossibility certificate, not a joint witness',
    'KernelCensus': 'typed census utility, not a premise witness',
    'ParseSignatures': 'syntax-span parser, not an elaborated theorem or witness',
    'RefutationFidelity': 'elaborated equality of original and refutation types',
    'Refutations': 'intentional refutation certificates preserve original telescopes',
    'Success': 'producer/composition controls with joint witnesses; no gas/fork or native execution adequacy',
}


def classify(root, rows):
    if not isinstance(rows, list):
        raise ValueError('invalid delta rows')
    root = Path(root).resolve()
    out, seen = [], set()
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get('path'), str):
            raise ValueError('invalid candidate')
        path = row['path']
        if not path.startswith(PREFIX):
            continue
        filename = path[len(PREFIX):]
        if not filename.endswith('.lean') or filename[:-5] not in ROLES or path in seen:
            raise ValueError('unreviewed or duplicate candidate')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from census')
        name = filename[:-5]
        effect = ('appends JSONL to configured h62.auditOutput when witness command runs; controls select a fixed absolute path and check declarations; acceptance reads records separately'
                  if name in ('DefaultWitnesses', 'DefaultWitnessControls') else
                  'reads a module list and writes requested JSONL including possible error rows when run; marker alone is not a clean census' if name == 'KernelCensus' else
                  'reads requested source files and prints parsed JSON when run' if name == 'ParseSignatures' else
                  'no file output established for direct elaboration; driver writes private logs and artifacts')
        out.append({'candidate': row, 'role': ROLES[name],
                    'driver': 'scripts/h62/item2/audit-yul/check_serial.py and audit-specific scripts are candidate references; current invocation unresolved',
                    'inputs': 'source/import closure, configured output and toolchain; exact current inputs unverified',
                    'effects': effect,
                    'expected_outcome': 'current execution unresolved; historical serial runner timeout is 1800s, not the H55 300s gate',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: audit_yul_controls.py STANDALONE_DELTA.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'delta-subset-only-unverified',
                          'input_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, data['delta']['added'])}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'audit Yul classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
