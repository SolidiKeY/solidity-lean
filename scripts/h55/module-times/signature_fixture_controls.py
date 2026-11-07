#!/usr/bin/env python3
"""Guard regression: signature or environment observations imply proof or loader provenance."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item1/duplication-scanner/'
ROLES = {
    'SignatureAxioms': 'guarded exact axiom-report diagnostics; expected successful elaboration',
    'SignatureConsumer': 'emits fixture signature records for comparison, not proof-body equality',
    'SignatureEnvironment': 'defines environment observation; does not authenticate loaded bytes or prevent ABA replacement',
    'SignatureEnvironmentProbe': 'invokes environment observation, not loader provenance attestation',
    'SignatureFingerprint': 'conservative type serialization; equality does not prove bodies, ownership or safe movement',
    'SignatureMissing': 'guarded unknown-constant diagnostic; expected successful elaboration',
    'SignatureObservedConsumer': 'invokes environment and signature observation, not execution attestation',
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
                    'driver': 'scripts/h62/item1/duplication-scanner/check_signature_fixture.sh lists all seven; current invocation unresolved',
                    'inputs': 'Lean 4.24, fresh private olean path, expected records and current import closure; exact inputs unverified',
                    'effects': 'driver writes private oleans, logs, status, preflight resource records and observation snapshots',
                    'expected_outcome': 'guarded negative diagnostics require successful exit; 120s per command is not H55 runner attestation',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: signature_fixture_controls.py REFERENCE_INDEX.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'supplied-snapshot-subset-only-unverified',
                          'input_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, data['rows'])}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'signature fixture classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
