#!/usr/bin/env python3
"""Guard regression: guarded negative diagnostics or a partial audit count as full coverage."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item2/audit-exact-verification/'
ROLES = {
    'BitArithAudit': 'concrete joint-input controls and axiom reports for bit arithmetic',
    'IndependentModuleCensus': 'module declaration census; unclassified declarations do not become witnesses',
    'JointWitness': 'constructs kernel-checked joint existential inputs under standard-axiom restriction',
    'JointWitnessControls': 'synthetic guarded missing-binder rejection, outside frozen interface census',
    'LinearDecisionAudit': 'concrete joint-input controls and axiom reports for linear decisions',
    'LinearHypothesesAudit': 'concrete joint-input and supported-projection controls',
    'RecoveryAudit': 'joint controls have empty tuples for two unconditional recovery declarations',
    'VisitedSetAudit': 'selected concrete joint bundles and rejection controls, not full census',
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
        driver = ('bounded-check.sh audit explicitly selects VisitedSetAudit; current applicability unresolved' if name == 'VisitedSetAudit'
                  else 'h70-check.py names this audit and uses --run opt-in; current invocation and prerequisites unresolved')
        out.append({'candidate': row, 'role': ROLES[name], 'driver': driver,
                    'inputs': 'separate Lean 4.35 environment, imports and private evidence; current bytes and availability unverified',
                    'effects': 'candidate driver writes private oleans, logs and receipts; direct elaboration effects unverified',
                    'expected_outcome': 'guarded negative diagnostic is expected success; historical timing STOP at 19.66% slowdown and 300s control is not H55 attestation',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: exact_audit_controls.py STANDALONE_DELTA.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'delta-subset-only-unverified',
                          'input_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, data['delta']['added'])}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'exact audit classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
