#!/usr/bin/env python3
"""SOL-OV external compiler gate; this is not a Lean soundness proof."""
import argparse
import hashlib
import itertools
import json
import re
from pathlib import Path
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
TESTS = ROOT / 'tests/sol-override-validation'
VERSION = '0.8.38+commit.1835d247.Emscripten.clang'
COMPILER_SHA = '6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390'


def fail(message):
    raise ValueError(message)


def validate(rows, evidence):
    if evidence.get('version') != VERSION or evidence.get('compilerSha256') != COMPILER_SHA:
        fail('compiler pin/version mismatch')
    ids = [r['id'] for r in rows]
    if len(ids) != len(set(ids)):
        fail('duplicate fixture ID')
    actual = evidence.get('rows', [])
    if [r.get('id') for r in actual] != ids:
        fail('missing, extra, reordered or mismatched result IDs')
    inventory = set()
    for row, result in zip(rows, actual):
        source = (TESTS / row['file']).resolve()
        if source.parent != (TESTS / 'fixtures').resolve():
            fail('fixture outside owned directory')
        if source in inventory:
            fail('duplicate fixture file')
        inventory.add(source)
        if hashlib.sha256(source.read_bytes()).hexdigest() != result.get('sourceSha256'):
            fail(row['id'] + ': source hash mismatch')
        if type(row['expected']) is not bool or type(result.get('accepted')) is not bool:
            fail(row['id'] + ': verdict is not a Boolean')
        if result['accepted'] != row['expected']:
            fail(row['id'] + ': compiler verdict differs from frozen expectation')
        errors = result.get('errors')
        if type(errors) is not list or any(type(e) is not dict or
                set(e) != {'code', 'type', 'message'} or
                (e['code'] is not None and type(e['code']) is not str) or
                type(e['type']) is not str or type(e['message']) is not str for e in errors):
            fail(row['id'] + ': malformed diagnostic list')
        if result['accepted'] != (errors == []):
            fail(row['id'] + ': inconsistent error/verdict record')
        if row.get('phase') not in ['override-control', 'invalid-declaration']:
            fail(row['id'] + ': missing coverage phase')
    if inventory != {p.resolve() for p in (TESTS / 'fixtures').glob('*.sol')}:
        fail('fixture inventory differs from matrix')
    vs = ['external', 'public', 'internal', 'private']
    ms = ['nonpayable', 'payable', 'view', 'pure']
    domain = set(itertools.product(vs, vs, ms, ms))
    for family in ['function', 'fallback', 'receive']:
        subset = [r for r in rows if r['family'] == family and r['dimensions']]
        values = [(r['dimensions']['baseVisibility'], r['dimensions']['derivedVisibility'],
                   r['dimensions']['baseMutability'], r['dimensions']['derivedMutability']) for r in subset]
        if len(values) != 256 or set(values) != domain:
            fail(family + ': incomplete or duplicate attribute matrix')
    getters = [r for r in rows if r['family'] == 'getter' and r['dimensions']]
    if len(getters) != 16 or {(r['dimensions']['baseVisibility'], r['dimensions']['baseMutability'])
                             for r in getters} != set(itertools.product(vs, ms)):
        fail('incomplete or duplicate getter attribute domain')
    required = json.loads((TESTS / 'required-controls.json').read_text())
    if not set(required).issubset(ids):
        fail('a required named control is missing')
    for family in ['function', 'fallback', 'receive', 'getter', 'modifier', 'pruning', 'diamond']:
        subset = [r for r in rows if r['family'] == family and r['phase'] == 'override-control']
        if {r['expected'] for r in subset} != {True, False}:
            fail(family + ': missing positive or negative override control')
    return len(rows)


def replay_inputs():
    paths = set()
    pending = [TESTS / 'CandidateReplay.lean', TESTS / 'CurrentChecker.lean']
    while pending:
        source = pending.pop()
        if source in paths:
            continue
        paths.add(source)
        for imports in re.findall(r'^import ([^\n]+)', source.read_text(), re.M):
            for module in imports.split('--', 1)[0].split():
                local = ROOT / (module.replace('.', '/') + '.lean')
                if local.is_file():
                    pending.append(local)
    paths.update(TESTS / p for p in ['matrix.json', 'required-controls.json',
        'CandidateReplay.lean', 'CurrentChecker.lean', 'compiler.mjs', 'replay.py',
        'evidence/compiler-matrix.json', 'evidence/serial-lakefile.toml'])
    paths.add(ROOT / 'scripts/check-sol-override-validation.py')
    paths.add(ROOT / 'lakefile.toml')
    paths.add(ROOT / 'lean-toolchain')
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}


def validate_serial_config(data):
    config = tomllib.loads(data.decode())
    if '-j1' not in config.get('weakLeanArgs', []):
        fail('effective package configuration lacks explicit -j1')
    if not config.get('lean_lib') or any('-j1' not in lib.get('weakLeanArgs', []) for lib in config['lean_lib']):
        fail('effective library configuration lacks explicit -j1')


def validate_replays(rows, manifest):
    validate_serial_config((TESTS / 'evidence/serial-lakefile.toml').read_bytes())
    if manifest.get('inputs') != replay_inputs():
        fail('replay inputs changed or are incomplete')
    if manifest.get('leanVersion') != 'Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)':
        fail('replay Lean pin mismatch')
    if manifest.get('threads') != 1 or manifest.get('memoryBytes') != 10737418240 or manifest.get('swapBytes') != 0:
        fail('replay resource bounds mismatch')
    build = manifest.get('build', {})
    build_log = TESTS / 'evidence/replay-build.log'
    if build.get('exitCode') != 0 or build.get('sha256') != hashlib.sha256(build_log.read_bytes()).hexdigest():
        fail('missing successful hash-bound dependency build')
    summary = {}
    for kind, filename in [('candidate', 'candidate-matrix.tsv'), ('current', 'current-checker.tsv')]:
        path = TESTS / 'evidence' / filename
        record = manifest.get(kind, {})
        if record.get('exitCode') != 0 or record.get('sha256') != hashlib.sha256(path.read_bytes()).hexdigest():
            fail(kind + ': missing successful hash-bound replay')
        lines = path.read_text().splitlines()
        if len(lines) != len(rows):
            fail(kind + ': row count mismatch')
        parsed = accepted = 0
        false_passes = {}
        for row, line in zip(rows, lines):
            fields = line.split('\t')
            if len(fields) != 4 or fields[0] != 'tests/sol-override-validation/' + row['file']:
                fail(kind + ': missing, reordered or malformed row')
            _, phase, verdict, detail = fields
            if phase not in ['parsed', 'parse-error']:
                fail(kind + ': unknown parse phase')
            if phase == 'parse-error':
                if verdict != '-' or detail != ('0' if kind == 'candidate' else '-'):
                    fail(kind + ': malformed parse refusal')
                if row['expected'] or row['phase'] == 'override-control':
                    fail(kind + ': required semantic control failed parsing')
                continue
            parsed += 1
            if verdict not in ['true', 'false']:
                fail(kind + ': malformed Boolean verdict')
            accepted += verdict == 'true'
            if kind == 'candidate':
                if not detail.isdecimal():
                    fail('candidate: malformed timing')
                if (verdict == 'true') != row['expected']:
                    fail(row['id'] + ': candidate/compiler mismatch')
            else:
                if detail not in ['true', 'false']:
                    fail('current: malformed placement verdict')
                if verdict == detail == 'true' and not row['expected']:
                    false_passes.setdefault(row['family'], []).append(row['id'])
        if kind == 'current' and not {'fallback', 'receive', 'getter', 'modifier'}.issubset(false_passes):
            fail('current: a documented false-pass family was not reproduced with wellFormedB=true')
        summary[kind] = dict(rows=len(rows), parsed=parsed, accepted=accepted, falsePasses=false_passes)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, help='rerun exact compiler instead of checking recorded results')
    parser.add_argument('--evidence', type=Path, default=TESTS / 'evidence/compiler-matrix.json')
    parser.add_argument('--write-evidence', action='store_true', help='save successful fresh compiler results')
    parser.add_argument('--replays', action='store_true', help='also validate hash-bound current and candidate replay evidence')
    args = parser.parse_args()
    rows = json.loads((TESTS / 'matrix.json').read_text())
    if args.write_evidence and not args.compiler:
        fail('--write-evidence requires --compiler')
    if args.compiler:
        if hashlib.sha256(args.compiler.read_bytes()).hexdigest() != COMPILER_SHA:
            fail('compiler byte hash mismatch')
        result = subprocess.run(['node', str(TESTS / 'compiler.mjs'), str(args.compiler.resolve()),
                                 str(TESTS / 'matrix.json')], check=True, text=True, capture_output=True, timeout=180)
        evidence = json.loads(result.stdout)
    else:
        evidence = json.loads(args.evidence.read_text())
    count = validate(rows, evidence)
    if args.write_evidence:
        args.evidence.write_text(json.dumps(evidence, indent=2) + '\n')
    print(f'PASS external compiler matrix: {count} rows; exact IDs, hashes, inventory and expectations')
    if args.replays:
        summary = validate_replays(rows, json.loads((TESTS / 'evidence/replay-manifest.json').read_text()))
        print('PASS replay parity and original false-pass reproduction: ' + json.dumps(summary, sort_keys=True))
    print('BOUNDARY: differential execution is external evidence; kernel equivalence and identity proofs are separate')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, subprocess.SubprocessError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
