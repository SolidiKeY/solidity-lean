#!/usr/bin/env python3
"""Collect the existing serial full-build queue; never starts Lean or edits Git.

A failed/resource-stopped attempt cannot yield an accepted speed ratio. Optional
waiting is bounded; completed outputs get a separate checksum manifest so no
running log is described as immutable evidence.
"""
import argparse
from decimal import Decimal
import hashlib
import json
import math
from pathlib import Path
import time

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
RULES = Path('/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key')
OLD_TOOLCHAIN = Path('/workspace/.setup/tools/lean-4.24.0-linux')
EXPECTED_LIMITS = {'virtual_address_limit_bytes': None, 'rss_watchdog_cap_bytes': 12 * 1024**3,
                   'vm_hard_memory_cap_bytes': 16 * 1024**3, 'reserve_bytes': 4 * 1024**3,
                   'threads': 1, 'swap_current_bytes': 0}


def load_pair(evidence):
    return {lane: json.loads((evidence / f'matched-rss-{lane}-result.json').read_text())
            for lane in ['old', 'new']}


def collect(evidence):
    evidence = evidence.resolve()
    results = load_pair(evidence)
    sources = {lane: json.loads((evidence / f'matched-rss-{lane}-sources.json').read_text())
               for lane in ['old', 'new']}
    old, new = results['old'], results['new']
    expected_command = ['env', f'SOLKEY_RULES={RULES}', 'bash', './run-lean.sh']
    if not RULES.is_file():
        raise RuntimeError('explicit frozen SolKey input is missing')
    for lane, version in [('old', '4.24.0'), ('new', '4.35.0')]:
        if sources[lane]['base'] != BASE or version not in sources[lane]['lean_version']:
            raise RuntimeError(f'{lane} has the wrong source base or toolchain version')
        if not sources[lane]['clean_build_dir_absent']:
            raise RuntimeError(f'{lane} was not prepared with an empty build directory')
        duration = results[lane]['wall_seconds']
        rss = results[lane]['aggregate_sampled_peak_rss_bytes']
        if not math.isfinite(duration) or duration <= 0 or not math.isfinite(rss) or rss <= 0:
            raise RuntimeError(f'{lane} has invalid duration or RSS')
        expected_toolchain = OLD_TOOLCHAIN if lane == 'old' else evidence / 'toolchains/lean-4.35.0-linux'
        if Path(results[lane]['cwd']).resolve() != evidence / f'matched-rss-{lane}':
            raise RuntimeError(f'{lane} result does not belong to its prepared snapshot')
        if Path(results[lane]['toolchain']).resolve() != expected_toolchain.resolve():
            raise RuntimeError(f'{lane} result uses the wrong prepared toolchain')
        if results[lane]['command'] != expected_command:
            raise RuntimeError(f'{lane} did not run the required full gate with explicit SolKey input')
        limits = results[lane]['limits']
        if limits != EXPECTED_LIMITS:
            raise RuntimeError(f'{lane} violates the fixed calibrated resource settings')
    if sources['old']['lean_sources'] != sources['new']['lean_sources']:
        raise RuntimeError('frozen source trees differ')
    if sources['old']['private_lakefile_sha256'] != sources['new']['private_lakefile_sha256']:
        raise RuntimeError('private Lake settings differ')
    if old['limits'] != new['limits'] or old['command'] != new['command']:
        raise RuntimeError('full-build commands or resource settings differ')
    both_pass = all(row['exit'] == 0 and row['resource_stop'] is None for row in results.values())
    delta = float((Decimal(str(new['wall_seconds'])) /
                   Decimal(str(old['wall_seconds'])) - 1) * 100) if both_pass else None
    exceeds_limit = (Decimal(str(new['wall_seconds'])) >
                     Decimal(str(old['wall_seconds'])) * Decimal('1.10')) if both_pass else None
    report = {
        'base': BASE, 'solkey_rules_sha256': hashlib.sha256(RULES.read_bytes()).hexdigest(), 'comparison_is_valid_successful_full_builds': both_pass,
        'full_wall_delta_percent': delta,
        'full_wall_slowdown_exceeds_10_percent': exceeds_limit,
        'full_sampled_RSS_delta_percent':
            100 * (new['aggregate_sampled_peak_rss_bytes'] /
                   old['aggregate_sampled_peak_rss_bytes'] - 1) if both_pass else None,
        'attempts': results,
        'status': 'blocked_failed_or_resource_stopped_gate' if not both_pass else
                  'stop_full_wall_slowdown_over_10_percent' if exceeds_limit else
                  'full_builds_passed_root_acceptance_pending',
        'per_module_policy': 'Per-module time/RSS increases are recorded and do not stop the lane.',
        'boundary': 'This result collects whole-repository build attempts. Failed or interrupted '
                    'attempt durations are retained but cannot establish a successful old/new '
                    'speed ratio. A passing collection is not root migration acceptance.'}
    output = evidence / 'matched-full-comparison.json'
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    paths = [output]
    for lane in ['old', 'new']:
        paths += [evidence / f'matched-rss-{lane}-result.json',
                  evidence / f'matched-rss-{lane}-result.log',
                  evidence / f'matched-rss-{lane}-sources.json']
    manifest = evidence / 'matched-full-comparison-SHA256SUMS'
    manifest.write_text('\n'.join(hashlib.sha256(path.read_bytes()).hexdigest() +
                                  '  ' + str(path) for path in sorted(paths)) + '\n')
    print(json.dumps({'status': report['status'], 'full_wall_delta_percent': delta,
        'full_wall_slowdown_exceeds_10_percent': exceeds_limit,
                      'output': str(output), 'checksums': str(manifest)}), flush=True)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--wait-seconds', type=float, default=0)
    args = parser.parse_args()
    if not math.isfinite(args.wait_seconds) or not 0 <= args.wait_seconds <= 28800:
        parser.error('--wait-seconds must be finite and between 0 and 28800')
    deadline = time.monotonic() + args.wait_seconds
    while True:
        try:
            load_pair(args.evidence)
            break
        except (FileNotFoundError, json.JSONDecodeError):
            if time.monotonic() >= deadline:
                raise SystemExit('PENDING: complete old/new result JSON files are not available')
            time.sleep(min(5, max(0, deadline - time.monotonic())))
    collect(args.evidence)
