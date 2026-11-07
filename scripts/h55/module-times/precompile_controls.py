#!/usr/bin/env python3
"""Guard regression: a printed precompile marker hides a failed native probe."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'Bridge/tests/precompile-agreement/'
ROLES = {
    'Acceptance': 'checks public imported names',
    'ActualAxioms': 'prints actual axiom reports; verifier compares them to explicit pins',
    'AllDeclarations': 'audits imported agreement declarations against permitted axioms',
    'Axioms': 'guards exact public axiom messages',
    'BoundaryVectors': 'computed core vectors, not cryptographic equality proofs; historical native FFI failure despite printed marker, exit 1',
    'CacheRequest': 'argument-driven cache-hash lookup tool, not a theorem',
    'NativeModexpProbe': 'native MODEXP guard; historical failure on missing external FFI symbols',
    'TrustProbe': 'prints selected Identity and Gas axiom reports',
}
VERIFIED_DRIVER = {'Acceptance', 'ActualAxioms', 'AllDeclarations', 'Axioms', 'BoundaryVectors'}


def classify(root, manifest):
    if not isinstance(manifest, dict) or not isinstance(manifest.get('rows'), list):
        raise ValueError('invalid census')
    root = Path(root).resolve()
    out, seen = [], set()
    for row in manifest['rows']:
        if not isinstance(row, dict) or not isinstance(row.get('path'), str):
            raise ValueError('invalid candidate')
        path = row['path']
        if not path.startswith(PREFIX):
            continue
        name = path[len(PREFIX):]
        if not name.endswith('.lean') or name[:-5] not in ROLES or path in seen:
            raise ValueError('unreviewed or duplicate candidate')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from census')
        name = name[:-5]
        included = name in VERIFIED_DRIVER
        out.append({'candidate': row, 'role': ROLES[name],
                    'driver': 'Bridge/tests/precompile-agreement/verify.py via run-file.py; applicability unverified' if included else 'unresolved current invocation; not in verify.py',
                    'inputs': 'Bridge workspace, pinned imports and setup; exact current inputs unverified',
                    'effects': 'verifier writes logs, receipt and producer oleans, and stops Lean MCP' if included else 'CacheRequest prints hashes when run' if name == 'CacheRequest' else 'unverified per invocation',
                    'expected_outcome': 'verifier requires successful exit, no warnings and matching pins; current execution unresolved' if included else 'current execution unresolved',
                    'status': 'static-reference-not-execution-acceptance'})
    return out


def main():
    if len(sys.argv) != 2:
        print('usage: precompile_controls.py CENSUS.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'unverified-subsets-accepted',
                          'census_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError) as exc:
        print(f'precompile classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
