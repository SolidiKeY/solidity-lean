#!/usr/bin/env python3
"""Guard regression: elaboration side effects or native observations count as proof passes."""
import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
CONTROLS = {
    'Bridge/tests/MemoryObserve.lean': {
        'context': 'Bridge Lake workspace; native observation, not PaddingCorrect proof',
        'driver': 'scripts/check-external-memory.sh; caller must hold writer lock and enforce bounds; applicability unverified',
        'inputs': 'pinned vendor FFI, memory-zeroes.c/hash, C compiler, Bridge oleans and generated shared library',
        'effects': 'driver writes generated C, ABI wrapper, shared library and build artifacts under Bridge/.lake/build',
        'outcome': 'main prints observations or throws; current invocation unresolved'},
    'scripts/AxiomAudit.lean': {
        'context': 'root Lake workspace; audit covers imported Solidity roots, not corpus or testsuite',
        'driver': '.github/workflows/lean.yml axiom audit; current applicability unverified',
        'inputs': 'built Solidity, SolidityExamples and SoliditySlowExamples imports',
        'effects': 'Lean audit logs errors and summary; build prerequisites may write artifacts',
        'outcome': 'audit logs errors on disallowed axioms, cycles or stale exemptions; current run unresolved'},
    'scripts/ParseCorpus.lean': {
        'context': 'root Lake workspace; #eval runs while elaborating',
        'driver': 'scripts/parse-corpus.mjs prepare and report; Lean elaboration between steps',
        'inputs': '.cache/parse-corpus/manifest.tsv and file paths named within it',
        'effects': 'writes .cache/parse-corpus/results.tsv; report --write updates baseline',
        'outcome': 'reports parse and roundtrip status per unit; current invocation unresolved'},
    'scripts/fixtures/backend-scalar-export.lean': {
        'context': 'root Lake workspace; #eval exports vectors, kernel controls and external EVM evidence are distinct',
        'driver': 'scripts/check-backend-scalar-evm.mjs consumes captured export; exact Lean invocation unresolved',
        'inputs': 'Lean imports; external checker requires export log and pinned EthereumJS node modules',
        'effects': '#eval prints JSON vectors; external checker prints results',
        'outcome': 'kernel vector theorems include an intentional negative vector; external checker is separate; current invocation unresolved'},
}


def classify(root, manifest):
    if not isinstance(manifest, dict) or not isinstance(manifest.get('rows'), list):
        raise ValueError('invalid census')
    root = pathlib.Path(root).resolve()
    found, seen = [], set()
    for row in manifest['rows']:
        if not isinstance(row, dict) or not isinstance(row.get('path'), str):
            raise ValueError('invalid candidate')
        path = row['path']
        if path not in CONTROLS:
            continue
        if path in seen:
            raise ValueError('duplicate candidate')
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError('invalid source')
        if hashlib.sha256(source.read_bytes()).hexdigest() != row.get('sha256'):
            raise ValueError('source differs from census')
        found.append({'candidate': row, **CONTROLS[path], 'status': 'static-reference-not-execution-acceptance'})
    return found


def main():
    if len(sys.argv) != 2:
        print('usage: root_controls.py CENSUS.json', file=sys.stderr)
        return 2
    try:
        raw = pathlib.Path(sys.argv[1]).read_bytes()
        print(json.dumps({'status': 'partial-static-classification-not-acceptance',
                          'coverage': 'unverified-subsets-accepted',
                          'census_sha256': hashlib.sha256(raw).hexdigest(),
                          'rows': classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError) as exc:
        print(f'root control classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
