#!/usr/bin/env python3
"""Run isolated audit and generated-import controls serially.

Caller holds the repository writer lock. LEAN must name the coordinator-pinned
Lean binary. This is an external test of the audit mechanism, not a proof of the
project's actual audit or a replacement for its build.
"""
import argparse
import hashlib
import json
import os
import pathlib
import resource
import subprocess
import tempfile
import time

import collect

ROOT = pathlib.Path(__file__).resolve().parents[4]
FIXTURE = ROOT / 'tests/h62/item1/trust-fragments/Fixture.lean'
ADDON = ROOT / 'tests/h62/item1/trust-fragments/FixtureAddon.lean'
ALLOW = '[``propext, ``Classical.choice, ``Quot.sound]'
NAME = '``Solidity.TrustFragmentsFixture.usesPropext'


def headroom():
    values = dict(line.split(':', 1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines())
    available = int(values['MemAvailable'].split()[0]) * 1024
    maximum = pathlib.Path('/sys/fs/cgroup/memory.max').read_text().strip()
    if maximum != 'max':
        current = int(pathlib.Path('/sys/fs/cgroup/memory.current').read_text())
        available = min(available, int(maximum) - current)
    if available < 4 * 1024 ** 3:
        raise RuntimeError('less than 4 GiB available memory')
    if int(values['SwapTotal'].split()[0]) != 0:
        raise RuntimeError('swap is enabled')


def limit_memory():
    limit = 12 * 1024 ** 3
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean', required=True, type=pathlib.Path)
    args = parser.parse_args()
    source = FIXTURE.read_text()
    assert source.count(ALLOW) == 1 and source.count(NAME) == 1
    # A synthetic baseline pin is used only in this isolated fixture process.
    collect.BASELINE_SHA256 = hashlib.sha256(source.encode()).hexdigest()
    with tempfile.TemporaryDirectory() as lane_tmp:
        lane_dir = pathlib.Path(lane_tmp) / 'fixture-lane'
        lane_dir.mkdir()
        data = {'imports': [], 'headlines': ['Solidity.TrustFragmentsFixture.alsoUsesPropext']}
        (lane_dir / 'extra.json').write_text(json.dumps(data))
        generated = collect.collect_lanes(source.encode(), pathlib.Path(lane_tmp)).decode()
        data['headlines'] = ['Solidity.TrustFragmentsFixture.missing']
        (lane_dir / 'extra.json').write_text(json.dumps(data))
        generated_missing = collect.collect_lanes(source.encode(), pathlib.Path(lane_tmp)).decode()
    with tempfile.TemporaryDirectory(prefix='h62-trust-fixture-') as tmp:
        tmp_root = pathlib.Path(tmp)
        module_dir = tmp_root / 'Solidity'
        module_dir.mkdir()
        addon = module_dir / 'FixtureAddon.lean'
        addon.write_bytes(ADDON.read_bytes())
        env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(tmp_root))

        def run(label, arguments, expect_success, diagnostic):
            headroom()
            process = subprocess.Popen([str(args.lean), '-j1', '--tstack=131072', *arguments],
                                       cwd=tmp_root, env=env, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True, preexec_fn=limit_memory)
            deadline = time.monotonic() + 120
            try:
                while True:
                    try:
                        output, _ = process.communicate(timeout=0.25)
                        break
                    except subprocess.TimeoutExpired:
                        headroom()
                        if time.monotonic() > deadline:
                            raise TimeoutError('fixture timed out')
            except BaseException:
                process.kill()
                process.communicate()
                raise
            print(f'{label}: exit={process.returncode}; expected diagnostic={diagnostic!r}')
            if (process.returncode == 0) != expect_success or diagnostic not in output:
                print(output)
                raise SystemExit(1)

        run('build_addon', ['-o', str(module_dir / 'FixtureAddon.olean'), str(addon)], True, '')
        with tempfile.TemporaryDirectory() as lane_tmp:
            lane_dir = pathlib.Path(lane_tmp) / 'fixture-lane'
            lane_dir.mkdir()
            data = {'imports': ['Solidity.FixtureAddon'], 'headlines': ['Solidity.TrustFragmentsAddon.witness']}
            (lane_dir / 'extra.json').write_text(json.dumps(data))
            imported = collect.collect_lanes(source.encode(), pathlib.Path(lane_tmp)).decode()
            data['imports'] = ['Solidity.MissingImport']
            (lane_dir / 'extra.json').write_text(json.dumps(data))
            missing_import = collect.collect_lanes(source.encode(), pathlib.Path(lane_tmp)).decode()
        controls = [
            ('positive', source, True, 'fixture passed'),
            ('generated_lane', generated, True, 'fixture passed'),
            ('generated_lane_with_import', imported, True, 'fixture passed'),
            ('generated_lane_missing_import', missing_import, False, 'Solidity.MissingImport'),
            ('generated_lane_missing', generated_missing, False, 'Unknown constant'),
            ('unexpected_dependency', source.replace(ALLOW, '[]'), False, 'unexpected axioms'),
            ('missing_declaration', source.replace(NAME, 'Name.mkSimple "missing_fixture_declaration"'), False, 'Unknown constant'),
        ]
        for label, text, expect_success, diagnostic in controls:
            file = tmp_root / (label + '.lean')
            file.write_text(text)
            run(label, [str(file)], expect_success, diagnostic)
    print('fixture controls passed')


if __name__ == '__main__':
    main()
