#!/usr/bin/env python3
"""Guard regression: inhabited target data implies joint premises or physical storage adequacy."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item2/audit-v10-storage/'
ROLES = {
    'GeneratedFamilyWitnesses': 'finite operation-generated transport, not physical execution or global hash injectivity',
    'KeyBoundsWitnesses': 'joint key-bound inputs, not live reads, source admission or physical hash separation',
    'LayoutWitnesses': 'finite mapping and array access, not source liveness or physical hash adequacy',
    'LoopWitnesses': 'populated intrinsic loop cases, not source, gas, fork or world adequacy',
    'PushWitnesses': 'joint push inputs, not source allocation identity or world rollback',
    'RepresentedWitnesses': 'populated local endpoint, not universal producer or source oracle',
    'SourceReadWitnesses': 'existing typed source read fixture, not address compiler or world relation',
    'SourceWriteWitnesses': 'existing source write fixture, not address compiler or world relation',
    'TargetInputWitnesses': 'data-input inhabitance with no logical hypotheses, not joint logical-premise or totality proof',
    'TargetReuseWitnesses': 'symbolic retained payload, not physical-word, gas, fork or rollback adequacy',
    'TargetTotality': 'symbolic target code generators, not source or physical-world totality',
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
        if not isinstance(path, str) or not path.startswith(PREFIX):
            continue
        filename = path[len(PREFIX):]
        if not filename.endswith('.lean') or filename[:-5] not in ROLES or path in seen or entry.get('state') != 'new-candidate':
            raise ValueError('unreviewed, duplicate or unexpected candidate')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from drift snapshot')
        out.append({'candidate': row, 'role': ROLES[filename[:-5]],
                    'driver': 'validate.sh/validate.py check prerequisites or dependencies only; current per-file driver unresolved',
                    'inputs': 'Lean 4.35 tools, isolated config and current import/cache closure; exact inputs unverified',
                    'effects': 'no direct file output established; validation writes private logs, cache and receipts',
                    'expected_outcome': 'current execution unresolved; historical validator has no wall deadline and its RLIMIT_AS is not an RSS cap',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: storage_audit_controls.py DRIFT.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'drift-subset-only-unverified',
                          'input_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, data['rows'])}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'storage audit classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
