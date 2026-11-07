#!/usr/bin/env python3
"""Guard regression: expected production rejection or sound survivor becomes a mutant kill."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h28-sol/mutation-testing/oracles/'
BASELINES = {'CallbackTacletBaseline','DivAssignBaseline','IfElseBaseline','LengthReadBaseline',
             'RootDeleteBaseline','RootIncBaseline','TransferBaseline','TransferDiamondBaseline'}
KILLS = {'BoundsZeroKill','CallbackTacletFailureKill','DivisionOperandsKill','IfElsePolarityKill',
         'IfThenPolarityKill','PushLastSlotKill','RootDeleteSkippedKill','RootIncSkipKill',
         'TransferDiamondTrueKill','TransferZeroKill'}
PRODUCTION = {'BoundsZeroOnProduction','DivisionOperandsOnProduction','PushLastSlotOnProduction','RootDeleteSkippedOnProduction'}
SOUND = {'LengthReevalSound'}


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
        if name not in BASELINES | KILLS | PRODUCTION | SOUND or path in seen:
            raise ValueError('unreviewed or duplicate candidate')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from reference snapshot')
        if name in BASELINES:
            role = 'baseline oracle for original rule context; expected outcome depends on runner phase'
        elif name in PRODUCTION:
            role = 'production semantic negative control; expected localized witness failure is not a mutant kill'
        elif name in SOUND:
            role = 'candidate universal sound-survivor proof, not a mutant kill'
        else:
            role = 'candidate mutant kill witness; historical or current success must be established per case'
        out.append({'candidate': row, 'role': role,
                    'driver': 'tests/h28-sol/mutation-testing/tools/mcprun.py assembles phase-specific scratch sources; exact current invocation unresolved',
                    'inputs': 'frozen manifest, target source, oracle text, scratch context and Lean server; current inputs unverified',
                    'effects': 'runner writes scratch modules, diagnostics, JSON records and summaries; direct source execution unverified',
                    'expected_outcome': ('historical cross-mutant sendWithCallbackBox.send-flag-true-to-false.1 was witness-failed; main callback-table.failed-send-flag-true was killed; current phase unresolved' if name == 'CallbackTacletFailureKill' else 'phase-dependent; current manifest, diagnostics and outcome unresolved'),
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: mutation_oracle_controls.py REFERENCE_INDEX.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'supplied-snapshot-subset-only-unverified',
                          'input_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, data['rows'])}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'mutation oracle classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
