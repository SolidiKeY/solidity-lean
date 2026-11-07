#!/usr/bin/env python3
"""Guard regression: carrier records and contradictions become joint compiler witnesses."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item2/audit-compiler-transport/'
ROLES = {
    'Audit': 'frozen-interface controls; limited allocating scoped-call success, no gas/fork adequacy',
    'AutoWitness': 'bounded constructive witness search; unsolved cases produce no theorem',
    'CarrierInventory': 'inventory of proof-bearing records, not proof of global inhabitation',
    'ExplicitCases': 'nonempty optimizer framework models, not Solidity bytecode adequacy',
    'H69': 'intentional contradictory tuples use impossibility, not inhabited joint witnesses',
    'JointHypotheses': 'existentially binds full telescopes of False-conclusion declarations; not an inhabitation claim',
    'NilFixture': 'single core-compiler input/output fixture, not general compiler adequacy',
    'OptimizerFixture': 'accepted and rejected equality-validator examples',
    'Reflect': 'elaborated census writer; syntactic binder classification is not a witness',
    'Witnesses': 'dependent simultaneous witness for selected compiler boundary, not global producer inhabitation',
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
        effects = ('audit command writes caller-selected JSON when invoked' if name in ('AutoWitness', 'CarrierInventory', 'Reflect')
                   else 'no direct file output established; driver may write evidence and oleans')
        out.append({'candidate': row, 'role': ROLES[name],
                    'driver': 'scripts/h62/item2/audit-compiler-transport/h69_validate.py lists all ten; current invocation unresolved',
                    'inputs': 'source/import closure, output paths, toolchain and cache; exact current inputs unverified',
                    'effects': effects,
                    'expected_outcome': 'current execution unresolved; historical 900s default is not the H55 300s gate and RLIMIT_AS is not an RSS cap',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: compiler_transport_controls.py STANDALONE_DELTA.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'delta-subset-only-unverified',
                          'input_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, data['delta']['added'])}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'compiler transport classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
