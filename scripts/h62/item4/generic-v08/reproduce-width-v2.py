#!/usr/bin/env python3
"""Isolated v2 width check at master4.24, through the existing bounded runner.

Frozen v1 source and its4.35 runner are neither imported nor certified.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
from census import ROOT, mask

VERSION = '4.24.0'
COMMIT = '797c613eb9b6d4ec95db23e3e00af9ac6657f24b'
SECONDS = 300
TARGET = 'tests/h62/item4/generic-v08/IntrinsicWidthsV2.lean'


def dependency_order(repo, root='Solidity.Source.Types'):
    visiting, visited, order = set(), set(), []
    def visit(module):
        if module in visiting:
            raise ValueError('cyclic import: ' + module)
        if module in visited:
            return
        if re.fullmatch(r'Solidity(?:\.[A-Za-z_][A-Za-z0-9_]*)+', module) is None:
            raise ValueError('unsupported local import: ' + module)
        path = repo / (module.replace('.', '/') + '.lean')
        if not path.is_file() or path.resolve() != path:
            raise ValueError('missing or redirected import: ' + module)
        visiting.add(module)
        for dep in re.findall(r'^import (\S+)', mask(path.read_text()), re.M):
            visit(dep)
        visiting.remove(module)
        visited.add(module)
        order.append(module)
    visit(root)
    return order


def checked_output(repo, output):
    output = output.resolve()
    if output == repo or repo in output.parents:
        raise ValueError('receipts/build output must be outside git')
    if output.exists():
        raise ValueError('output must be fresh; existing receipts are preserved')
    return output


def version_matches(text):
    return ('version ' + VERSION + ',') in text and ('commit ' + COMMIT + ',') in text


def bounded_command(lean, record, seconds, args):
    if not 1 <= seconds <= SECONDS:
        raise ValueError('remaining budget must be between1 and300 seconds')
    return [sys.executable, '-B', str(ROOT/'scripts/h62/item4/generic-v08/bounded.py'),
            '--record', str(record), '--seconds', str(seconds), '--aggregate', '--aggregate-parent', '--parent-pid', str(os.getpid()), '--',
            str(lean), '-j1', '--tstack=131072', *args]


def input_bindings(repo, paths):
    result = {}
    for name in paths:
        path = repo/name
        if path.resolve() != path or not path.is_file():
            raise ValueError('missing or redirected input: ' + name)
        result[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def run_monitor(command, **kwargs):
    """Retain caller's writer lock until monitor cleanup is complete."""
    child = None
    previous = {}
    def interrupted(signum, _frame):
        raise InterruptedError('driver signal ' + str(signum))
    for signum in (signal.SIGTERM, signal.SIGINT):
        previous[signum] = signal.signal(signum, interrupted)
    try:
        child = subprocess.Popen(command, **kwargs)
        return subprocess.CompletedProcess(command, child.wait())
    except BaseException:
        for signum in previous:
            signal.signal(signum, signal.SIG_IGN)
        if child is not None:
            if child.poll() is None:
                child.terminate()
            child.wait()
        raise
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--toolchain', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(argv)
    start = time.monotonic()
    try:
        output = checked_output(ROOT, args.output)
        lean = (args.toolchain/'bin/lean').resolve(strict=True)
        if (ROOT/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v' + VERSION:
            raise ValueError('master toolchain differs from explicit v2 pin')
        version = subprocess.check_output([str(lean), '--version'], text=True, timeout=10)
        if not version_matches(version):
            raise ValueError('v2 requires Lean4.24.0 commit ' + COMMIT)
        modules = dependency_order(ROOT)
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        parser.error(str(error))
    output.mkdir(parents=True, exist_ok=False)
    (output/'version.txt').write_text(version)
    lockpath = Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
    lockpath.parent.mkdir(parents=True, exist_ok=True)
    with lockpath.open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        env = dict(os.environ, LEAN_PATH=str(output/'lib'), LEAN_NUM_THREADS='1',
                   PYTHONDONTWRITEBYTECODE='1', LEAN_SYSROOT=str(lean.parent.parent))
        bound_paths = [m.replace('.', '/')+'.lean' for m in modules] + [TARGET,
            'lean-toolchain', 'scripts/h62/item4/generic-v08/census.py',
            'scripts/h62/item4/generic-v08/bounded.py',
            'scripts/h62/item4/generic-v08/width_resources.py',
            'scripts/h62/item4/generic-v08/reproduce-width-v2.py',
            'scripts/h62/item4/generic-v08/check-width-v2.sh']
        before = input_bindings(ROOT, bound_paths)
        (output/'inputs-before.json').write_text(json.dumps(before, indent=2)+'\n')
        commands = []
        for module in modules:
            target = output/'lib'/(module.replace('.', '/')+'.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            commands.append((module, ['-o', str(target), module.replace('.', '/')+'.lean']))
        commands.append(('IntrinsicWidthsV2', [TARGET]))
        for name, command in commands:
            remaining = int(SECONDS-(time.monotonic()-start))
            if remaining < 1:
                (output/'STOP.txt').write_text('overall300second deadline exhausted\n')
                return 1
            run = bounded_command(lean, output/(name+'.json'), remaining, command)
            try:
                with (output/(name+'.log')).open('w') as log:
                    result = run_monitor(run, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                                         pass_fds=(lock.fileno(),))
            except BaseException as error:
                (output/'STOP.txt').write_text('driver interrupted after monitor cleanup: '+type(error).__name__+'\n')
                return 1
            print(name, result.returncode, flush=True)
            after = input_bindings(ROOT, bound_paths)
            (output/'inputs-after.json').write_text(json.dumps(after, indent=2)+'\n')
            if after != before:
                (output/'STOP.txt').write_text('input byte drift during check\n')
                return 1
            if time.monotonic()-start > SECONDS:
                (output/'STOP.txt').write_text('overall300second execution deadline exceeded\n')
                return 1
            if result.returncode:
                return result.returncode
        if time.monotonic()-start > SECONDS:
            (output/'STOP.txt').write_text('overall300second execution deadline exceeded\n')
            return 1
        (output/'summary.json').write_text(json.dumps(dict(status='V2_ONLY_PASS',
            wall_seconds=time.monotonic()-start, overall_seconds_limit=SECONDS,
            toolchain=VERSION, commit=COMMIT, input_sha256=before,
            deadline_observation='No pass accepted after observed deadline; monitor polling0.25s and failed-check termination grace up to5s',
            frozen_v1='UNCHANGED_AND_UNRESOLVED'), indent=2)+'\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
