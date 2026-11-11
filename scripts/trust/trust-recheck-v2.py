#!/usr/bin/env python3
"""Optional additive checker candidate; never invoked by CI or frozen v1.

Guards against relabelling a changed checker as the official pinned binary,
omitting proof objects, or resetting the total comparison deadline. Owner review
must bind the packet, binary and derived commit before one changed comparison.
The external serial/no-swap/memory/pidfd guard remains required. Telemetry is a
maximum of 128 dependency samples, not an exact in-flight kernel declaration.
No performance or fresh-replay acceptance is implied by building this candidate.
"""
import argparse
from dataclasses import replace
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import time

BASE = 'da26eb05e9959402afcb9bd6dfe5dc4f700f70d6'
RECIPE_SHA = '623c5ca18746942891869f169b90a665ac66ba4f6dac1edcbe251fff7cc0d0b4'
PATCH_SHA = '06309fdb9b6b786422d6a272d97aca57baa38e6efa6f8f53abee6f0ca846b0ac'
DOMAIN_SHA = 'd02bb29d6157625e5e12bc2a53f878d3efa437daff8031f269a8ed1a0f167028'
SOURCES = {
    'Main.lean': 'd73db540ff418bba732561502bda86b1ea3f853cef39ede62ed5b386d81007bd',
    'Lean4Checker/Replay.lean': '4a04f64b19afd9ec36c268fbbd2ea81f293e9e64cb9bd7e63101fb6c8a01e245',
}


def recipe():
    path = Path(__file__).resolve().parents[1] / 'trust-replay/recipe.py'
    if hashlib.sha256(path.read_bytes()).hexdigest() != RECIPE_SHA:
        raise ValueError('reviewed reference recipe changed')
    spec = importlib.util.spec_from_file_location('va1_reference_recipe', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def validate_binding(r, binding, expected, config, deadline):
    data = r.load_json(binding, expected, deadline)
    r.require(set(data) == {'schema', 'base', 'patch_sha256', 'checker_revision',
                          'checker_sha256', 'head', 'packet_sha256', 'manifest_sha256'},
              'unexpected owner binding fields')
    r.require(type(data['schema']) is int and data['schema'] == 1 and data['base'] == BASE
              and data['patch_sha256'] == PATCH_SHA, 'candidate provenance mismatch')
    for key in ('checker_sha256', 'packet_sha256', 'manifest_sha256'):
        r.require(isinstance(data[key], str) and re.fullmatch('[0-9a-f]{64}', data[key]), 'invalid hash')
    for key in ('checker_revision', 'head'):
        r.require(isinstance(data[key], str) and re.fullmatch('[0-9a-f]{40}', data[key]), 'invalid revision')
    r.require(data['checker_revision'] != BASE, 'v2 must have its own derived source identity')
    patch = Path(__file__).with_name('trust-checker-v2.patch')
    r.require(r.digest(patch, deadline) == PATCH_SHA, 'candidate patch changed')
    git = ['git', '--no-replace-objects']
    source = Path(config.checker_source)
    changed = r.small(git + ['diff', '--name-only', BASE, data['checker_revision']], source, deadline)
    r.require(set(changed.splitlines()) == set(SOURCES), 'unexpected checker source changes')
    r.small(git + ['merge-base', '--is-ancestor', BASE, data['checker_revision']], source, deadline)
    for name, sha in SOURCES.items():
        r.require(r.digest(source / name, deadline) == sha, 'unreviewed checker source: ' + name)
    packet = r.load_json(config.packet, data['packet_sha256'], deadline)
    manifest = r.load_json(config.manifest, data['manifest_sha256'], deadline)
    rows = [{key: row[key] for key in ('path', 'sha256', 'bytes')} for row in manifest['files']]
    domain = hashlib.sha256(json.dumps(sorted(rows, key=lambda row: row['path']),
                                      sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    r.require(domain == DOMAIN_SHA, 'public proof object domain changed; renewed review required')
    r.require(manifest == packet['manifest_content'], 'packet/manifest mismatch')
    # This bounded candidate is deliberately restricted to the original proof
    # domain. A growing/changed public setup requires a new reviewed binding,
    # rather than silently reducing or extending this comparison's allowance.
    return replace(r.REFERENCE, packet_sha256=data['packet_sha256'],
                   manifest_sha256=data['manifest_sha256'], checker_sha256=data['checker_sha256'],
                   checker_revision=data['checker_revision'], head=data['head'])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binding', required=True, type=Path)
    p.add_argument('--binding-sha256', required=True)
    for option in ('packet', 'manifest', 'objects', 'source-root', 'checker', 'checker-source', 'sysroot', 'output'):
        p.add_argument('--' + option, required=True, type=Path)
    args = p.parse_args()
    deadline = time.clock_gettime(time.CLOCK_BOOTTIME) + 300
    r = recipe()
    binding, expected = args.binding, args.binding_sha256
    del args.binding, args.binding_sha256
    try:
        profile = validate_binding(r, binding, expected, args, deadline)
        # The reference runner receives only the remaining allowance. Its full
        # pre/post hashes, toolchain, source, kernel flag and refusals stay intact.
        code = r.run(replace(profile, seconds=r.remaining(deadline)), args)
        if code == 0:
            r.load_json(binding, expected, deadline)
            r.remaining(deadline)
        return code
    except (r.InvalidInput, ValueError, OSError, KeyError, TypeError) as error:
        print('v2 refused: ' + str(error), file=sys.stderr)
        return 2
    except (r.Deadline, r.subprocess.TimeoutExpired) as error:
        print('v2 deadline: ' + str(error), file=sys.stderr)
        return 124


if __name__ == '__main__':
    raise SystemExit(main())
