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
import signal
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
    limit = 8 * 1024 ** 3
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))


def pinned_tools(lean, archive=None, lake=None):
    lean = pathlib.Path(lean).resolve()
    extraction = lean.parent.parent
    archive = pathlib.Path(archive).resolve() if archive is not None else pathlib.Path(str(extraction) + '.tar.zst')
    expected = archive.parent / 'lean-4.35.0-linux/bin'
    if lean != expected / 'lean' or (lake is not None and pathlib.Path(lake).resolve() != expected / 'lake'):
        raise ValueError('toolchain paths do not match the pinned archive extraction')
    digest = hashlib.sha256()
    with archive.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    if digest.hexdigest() != '7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d':
        raise ValueError('official toolchain archive checksum mismatch')
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    if 'version 4.35.0' not in version or 'eb6cafb' not in version:
        raise ValueError('toolchain does not match pinned Lean 4.35.0 release')
    return version


def run_bounded(command, cwd, env, timeout):
    """One bounded process group; never leave a lake/Lean child after abort."""
    headroom()
    started = time.monotonic()
    process = subprocess.Popen(command, cwd=cwd, env=env,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               text=True, preexec_fn=limit_memory, start_new_session=True)
    try:
        while True:
            try:
                output, _ = process.communicate(timeout=0.25)
                break
            except subprocess.TimeoutExpired:
                headroom()
                if time.monotonic() - started > timeout:
                    raise TimeoutError('bounded Lean process timed out')
        headroom()
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.communicate()
        raise
    return process.returncode, output, time.monotonic() - started


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean', required=True, type=pathlib.Path)
    parser.add_argument('--archive', type=pathlib.Path, help='official archive; defaults beside the extraction')
    args = parser.parse_args()
    print(pinned_tools(args.lean, args.archive))
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
            code, output, _ = run_bounded(
                [str(args.lean), '-j1', '--tstack=131072', *arguments], tmp_root, env, 120)
            print(f'{label}: exit={code}; expected diagnostic={diagnostic!r}')
            if (code == 0) != expect_success or diagnostic not in output:
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
