#!/usr/bin/env python3
"""Standalone reproduction/coverage acceptance for the proposed migration.

Checks the frozen source and patch, then independently accounts for every
additive input. It does not establish Lean elaboration or producer ownership.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import tempfile

import accept_baseline
import collect
import lane_history

PATCH = collect.ROOT / 'scripts/h62/item1/trust-fragments/migration.patch'


def coverage(original, candidate, files):
    if hashlib.sha256(original).hexdigest() != accept_baseline.SHA256:
        raise ValueError('frozen baseline checksum mismatch')
    old_imports = set(re.findall(rb'(?m)^import (\S+)', original))
    imports, additions = set(), []
    for path, data in sorted(files.items(), key=lambda row: tuple(row[0].split('/', 1))):
        item = json.loads(data.decode('utf-8'))
        imports.update(x.encode() for x in item['imports'] if x.encode() not in old_imports)
        additions.extend(x.encode() for x in item['headlines'])
    prefix = b''.join(b'import ' + name + b'\n' for name in sorted(imports))
    start = original.index(b'  let headlines : List Name := [')
    end = original.index(b']', start)
    appended = b''.join(b',\n    ``' + name for name in additions)
    expected = collect.MARKER + prefix + original[:end] + appended + original[end:]
    if candidate != expected:
        raise ValueError('generated migration does not cover exactly the supplied inputs')
    # This equality checks all original commands, allowlists, duplicates,
    # imports and print reports, not only headline counts.
    restored = candidate[len(collect.MARKER) + len(prefix):]
    restored = restored[:end] + restored[end + len(appended):]
    if restored != original:
        raise ValueError('migration did not preserve every original byte')
    return {'baseline_sha256': accept_baseline.SHA256,
            'new_imports': len(imports), 'new_headlines': len(additions),
            'generated_sha256': hashlib.sha256(candidate).hexdigest()}


def read_commit_audit(head):
    return subprocess.check_output(['git', 'show', f'{head}:TrustAudit.lean'], cwd=collect.ROOT)


def accept(lane_root, candidate=None, require_installed=False, prior_commit=None):
    original = subprocess.check_output(['git', 'show', f'{accept_baseline.BASE}:TrustAudit.lean'], cwd=collect.ROOT)
    fragments = collect.collect(collect.FRAGMENTS)
    accept_baseline.accept(original, fragments, original)
    checked_in = collect.AUDIT.read_bytes()
    with tempfile.TemporaryDirectory(prefix='h62-migration-patch-') as tmp:
        source = pathlib.Path(tmp) / 'original.lean'
        source.write_bytes(original)
        applied = pathlib.Path(tmp) / 'TrustAudit.lean'
        result = subprocess.run(['patch', '--silent', '--output', str(applied),
                                 str(source), str(PATCH)], capture_output=True, text=True)
        if result.returncode or applied.read_bytes() != collect.MARKER + original:
            raise ValueError(f'migration patch does not reproduce the marked baseline: {result.stderr}')
    snapshot = lane_history.read_current_files(lane_root)
    generated = collect.MARKER + collect.collect_lane_snapshot(fragments, snapshot)
    if checked_in not in (original, generated):
        raise ValueError('checkout audit is neither the original nor the generated migration')
    if require_installed and checked_in != generated:
        raise ValueError('generated migration is not installed in the checkout')
    if require_installed and prior_commit is None:
        raise ValueError('installed gate requires the coordinator-approved prior commit')
    head = None
    committed = None
    if require_installed:
        if lane_root.resolve() != collect.LANES.resolve():
            raise ValueError('installed gate requires the canonical lane directory')
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=collect.ROOT).decode().strip()
        committed = lane_history.read_commit_files(head)
        if committed != snapshot:
            raise ValueError('lane inputs do not match committed HEAD')
        if read_commit_audit(head) != generated:
            raise ValueError('installed audit does not match committed HEAD')
    if prior_commit is not None:
        prior = lane_history.read_commit(prior_commit)
        lane_history.preserve(prior, lane_history.inventory_from_files(snapshot))
    if candidate is not None and candidate != generated:
        raise ValueError('candidate does not match generated migration')
    result = coverage(original, generated if candidate is None else candidate, snapshot)
    if collect.collect(collect.FRAGMENTS) != fragments:
        raise ValueError('raw fragments changed during acceptance')
    if lane_history.read_current_files(lane_root) != snapshot:
        raise ValueError('lane inputs changed during acceptance')
    if collect.AUDIT.read_bytes() != checked_in:
        raise ValueError('checkout audit changed during acceptance')
    if require_installed:
        final_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=collect.ROOT).decode().strip()
        if final_head != head:
            raise ValueError('HEAD or lane inputs changed during acceptance')
    result['checkout_state'] = 'original' if checked_in == original else 'migrated'
    result['prior_commit'] = prior_commit
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lanes', type=pathlib.Path, default=collect.LANES)
    parser.add_argument('--candidate', type=pathlib.Path)
    parser.add_argument('--prior-commit', help='full SHA of the coordinator-approved prior lane state')
    parser.add_argument('--require-installed', action='store_true',
                        help='fail unless the checkout contains the generated audit')
    args = parser.parse_args()
    try:
        data = None if args.candidate is None else args.candidate.read_bytes()
        result = accept(args.lanes, data, require_installed=args.require_installed, prior_commit=args.prior_commit)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        parser.exit(1, f'migration acceptance failed: {exc}\n')
    print(json.dumps({'status': 'pass', **result}, sort_keys=True))


if __name__ == '__main__':
    main()
