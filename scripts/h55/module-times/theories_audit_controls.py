#!/usr/bin/env python3
"""Guard regression: an intentional finite-shape impossibility becomes a witness."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item2/audit-theories/'
ROLES = {
    'CompilerAdmission': 'concrete public-entry bool admission; not gas, fork or byte-failure adequacy',
    'CoreTotality': 'core compiler success under separately discharged concrete hypotheses; not general machine observability',
    'ElaboratedCensus': 'elaborated inventory, not proof that every declaration has a witness',
    'FailureGasForkBoundary': 'source and core failure/gas/fork boundary; not measured EVM gas',
    'FiniteBoundary': 'intentional unsatisfiable joint-input domain, not a joint witness',
    'MirrorWitnesses': 'populated memory-mirror joint inputs; model feasibility, not physical gas',
    'PathRemaining': 'path joint inputs and abstract observations, not storage realizability',
    'PathWitnesses': 'dependent typed-path joint inputs with quantified frame premise',
    'ProgressWitnesses': 'selected progress input tuples, not source fuel as EVM gas',
    'ScopeControls': 'exact-input and global-versus-per-input controls, not new frozen premises',
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
        effect = ('census requires absolute off-checkout H62_AUDIT_CENSUS_OUT and writes or overwrites it after path checks' if name == 'ElaboratedCensus'
                  else 'no direct file output established; candidate driver writes private artifacts')
        out.append({'candidate': row, 'role': ROLES[name],
                    'driver': 'scripts/h62/item2/audit-theories/serial_check.py and verifier scripts are candidate references; exact current invocation unresolved',
                    'inputs': 'source/import closure, configured output, toolchain and cache; current inputs unverified',
                    'effects': effect,
                    'expected_outcome': 'current execution unresolved; historical 300s runner is not H55 runtime attestation; RLIMIT_AS is not an RSS cap',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: theories_audit_controls.py STANDALONE_DELTA.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'delta-subset-only-unverified',
                          'input_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, data['delta']['added'])}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'theories audit classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
