#!/usr/bin/env python3
"""Paired real-audit timing, with a hard stop at a measured >10% slowdown.

Run only after building all imports with the coordinator-pinned toolchain.
The repository writer lock is held for the whole measurement. This script never
changes the central audit and never treats a failed Lean run as timing evidence.
"""
import argparse
import fcntl
import hashlib
import json
import os
import pathlib
import subprocess
import tempfile
import time

import accept_baseline
import check_fixture
import collect

LOCK = pathlib.Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')


def snapshot():
    state = subprocess.check_output(['git', 'status', '--porcelain'], cwd=collect.ROOT)
    if state:
        raise RuntimeError('worktree must be clean for timing')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=collect.ROOT).decode().strip()
    build = collect.ROOT / '.lake/build/lib/lean'
    if not build.is_dir():
        raise RuntimeError('project build artifacts are absent')
    digest = hashlib.sha256()
    entries = sorted(build.rglob('*.olean'))
    if not entries:
        raise RuntimeError('project build artifacts are absent')
    for entry in entries:
        stat = entry.stat()
        digest.update(f'{entry.relative_to(build)}\0{stat.st_size}\0{stat.st_mtime_ns}\n'.encode())
    return {'head': head, 'olean_metadata_sha256': digest.hexdigest(), 'oleans': len(entries)}


def is_slow(baseline, candidate):
    if baseline <= 0 or candidate <= 0:
        raise ValueError('timings must be positive')
    return candidate > baseline * 1.10


def run_one(lake, lean, source):
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    command = [str(lake), 'env', str(lean), '-j1', '--tstack=131072', str(source)]
    code, output, elapsed = check_fixture.run_bounded(command, collect.ROOT, env, 1800)
    if code:
        raise RuntimeError(f'Lean audit failed ({code}):\n{output}')
    return elapsed, output


def audit_inputs(lanes):
    baseline = subprocess.check_output(['git', 'show', f'{accept_baseline.BASE}:TrustAudit.lean'], cwd=collect.ROOT)
    reconstructed = collect.collect(collect.FRAGMENTS)
    accept_baseline.accept(baseline, reconstructed, baseline)
    candidate = collect.MARKER + collect.collect_lanes(reconstructed, lanes)
    if collect.AUDIT.read_bytes() not in (baseline, candidate):
        raise ValueError('checkout audit is neither the original nor generated migration')
    return baseline, candidate


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean', type=pathlib.Path, required=True)
    parser.add_argument('--lake', type=pathlib.Path, required=True)
    parser.add_argument('--output-dir', type=pathlib.Path, required=True)
    parser.add_argument('--archive', type=pathlib.Path, required=True)
    args = parser.parse_args()
    check_fixture.pinned_tools(args.lean, args.archive, args.lake)
    archive = args.archive.resolve()
    digest = hashlib.sha256()
    with archive.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    if digest.hexdigest() != '7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d':
        raise RuntimeError('official toolchain archive checksum mismatch')
    expected_bin = archive.parent / 'lean-4.35.0-linux/bin'
    if args.lean.resolve() != expected_bin / 'lean' or args.lake.resolve() != expected_bin / 'lake':
        raise RuntimeError('toolchain paths do not match the pinned archive extraction')
    lean_version = subprocess.check_output([str(args.lean), '--version'], text=True).strip()
    lake_version = subprocess.check_output([str(args.lake), '--version'], text=True).strip()
    if 'version 4.35.0' not in lean_version or 'eb6cafb' not in lean_version or 'eb6cafb' not in lake_version:
        raise RuntimeError('toolchain does not match pinned Lean 4.35.0 release')
    output_dir = args.output_dir.resolve()
    if output_dir.is_relative_to(collect.ROOT):
        raise ValueError('timing evidence must be outside the checkout')
    output_dir.mkdir(parents=True, exist_ok=False)
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    with LOCK.open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        initial = snapshot()
        baseline, candidate = audit_inputs(collect.LANES)
        with tempfile.TemporaryDirectory(prefix='h62-trust-timing-') as tmp:
            baseline_path = pathlib.Path(tmp) / 'Baseline.lean'
            candidate_path = pathlib.Path(tmp) / 'Candidate.lean'
            baseline_path.write_bytes(baseline)
            candidate_path.write_bytes(candidate)
            pairs = []
            for index in range(3):
                order = [('baseline', baseline_path), ('candidate', candidate_path)]
                if index % 2:
                    order.reverse()
                results = {}
                for name, path in order:
                    if snapshot() != initial:
                        raise RuntimeError('checkout or build artifact metadata changed')
                    elapsed, output = run_one(args.lake, args.lean, path)
                    results[name] = elapsed
                    (output_dir / f'{index}-{name}.txt').write_text(output)
                    if snapshot() != initial:
                        raise RuntimeError('checkout or build artifact metadata changed')
                pairs.append(results)
                print(json.dumps({'pair': index, **results}), flush=True)
                if is_slow(results['baseline'], results['candidate']):
                    raise RuntimeError('candidate exceeded baseline by more than 10%; stopped')
    print(json.dumps({'result': 'pass', 'snapshot': initial, 'lean': lean_version,
                      'lake': lake_version, 'pairs': pairs}, sort_keys=True))


if __name__ == '__main__':
    main()
