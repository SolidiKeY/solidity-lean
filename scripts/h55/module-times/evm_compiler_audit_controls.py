#!/usr/bin/env python3
"""Guard regression: compiler audit impossibility is misreported as an inhabited witness."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item2/audit-evm-compiler/'
ROLES = {
    'HeadlineAudit': 'selected nonempty intrinsic compiler headline fixtures, not full compiler coverage',
    'IntentionalAudit': 'intentional refutation audit of selected imported original statements, not joint inhabitation',
    'JointImpossible': 'constructs negated existential packages only for terminal False; intentionality is separate metadata',
    'JumpdestAudit': 'local authored Jumpdest joint-input controls, not global producer coverage',
    'LayoutAudit': 'simultaneous impossibility controls for separation lemmas, not positive witnesses',
    'OpcodeAudit': 'fixed Osaka opcode-domain controls, not execution gas or historical-fork admission',
    'SuccessAudit': 'nonempty intrinsic compiler success and trivial-compiler rejection, not full EVM gas/fork adequacy',
}
MEASURED_ROOTS = {'LayoutAudit', 'SuccessAudit', 'HeadlineAudit'}


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
        if not isinstance(path, str) or not path.startswith(PREFIX) or entry.get('status') != 'no-supplied-current-reference':
            continue
        filename = path[len(PREFIX):]
        name = filename[:-5] if filename.endswith('.lean') else ''
        if name not in ROLES or path in seen:
            raise ValueError('unreviewed or duplicate candidate')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from reference snapshot')
        driver = ('scripts/h62/item2/audit-evm-compiler/measure.py names this root; current applicability unresolved'
                  if name in MEASURED_ROOTS else 'current dedicated per-file driver unresolved; historical manifest names source')
        out.append({'candidate': row, 'role': ROLES[name], 'driver': driver,
                    'inputs': 'source/import closure, configured toolchain and private evidence; current inputs unverified',
                    'effects': 'no direct file output established; candidate drivers write private logs and evidence',
                    'expected_outcome': 'current execution unresolved; historical resource controls do not attest H55 runtime acceptance',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: evm_compiler_audit_controls.py REFERENCE_INDEX.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'supplied-snapshot-subset-only-unverified',
                          'input_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, data['rows'])}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'EVM compiler audit classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
