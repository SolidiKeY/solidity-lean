#!/usr/bin/env python3
"""Serial source-only H64 PassCorrect check in an isolated, off-Git artifact cache.

This is an affected-module check, not the repository's final acceptance gate.
Every repository import is rebuilt; old .lake oleans are never consumed.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]
RESERVE = 4 * 1024**3
CAP = 8 * 1024**3
BUDGET = 300


def available():
    return int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines()
                    if line.startswith('MemAvailable:'))) * 1024


def bounds():
    resource.setrlimit(resource.RLIMIT_AS, (CAP, CAP))
    resource.setrlimit(resource.RLIMIT_CPU, (BUDGET, BUDGET))


def prepare_evidence(evidence):
    # An existing run is immutable: even early failures cannot leave old passes.
    evidence.mkdir(parents=True, exist_ok=False)
    (evidence / 'run-status.json').write_text(json.dumps(dict(status='pending'))+'\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--root', default='Solidity.Roadmap.G49Final.FoldedPublic')
    parser.add_argument('--controls', type=Path, default=Path('tests/h55/g49-final-theorem/PassCorrectControls.lean'))
    args = parser.parse_args()
    evidence = args.evidence.resolve()
    if evidence.is_relative_to(ROOT):
        parser.error('evidence/cache must be outside the repository')
    prepare_evidence(evidence)
    cache = evidence / 'cache'
    cache.mkdir(exist_ok=True)
    lock_path = Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        subprocess.run(['git', 'status', '--short', '--branch'], cwd=ROOT, check=True)
        if int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines()
                    if line.startswith('SwapTotal:'))) != 0:
            raise SystemExit('swap is enabled: no check started')
        ordered, visiting, done = [], set(), set()

        def visit(module):
            if module in visiting:
                raise ValueError('cyclic imports: ' + module)
            if module in done:
                return
            source = ROOT / (module.replace('.', '/') + '.lean')
            if not source.is_file():
                raise ValueError('missing source import: ' + module)
            visiting.add(module)
            for line in source.read_text().splitlines():
                if line.startswith('import '):
                    match = re.fullmatch(r'import (Solidity\.[A-Za-z0-9_.]+)\s*', line)
                    if match is None:
                        raise ValueError('unsupported import syntax in ' + str(source))
                    visit(match.group(1))
            visiting.remove(module)
            done.add(module)
            ordered.append((module, source))

        visit('Solidity.KeySort')
        visit(args.root)
        records = []
        for module, source in ordered:
            if available() < RESERVE:
                raise SystemExit('4 GiB reserve unavailable: no job started')
            output = cache / (module.replace('.', '/') + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            command = [str(args.lean.resolve()), '-j1', '--tstack=131072', '-o', str(output),
                       str(source.relative_to(ROOT))]
            started, reason, minimum = time.monotonic(), None, available()
            log_path = evidence / (module + '.log')
            with log_path.open('w') as log:
                job = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                       env={**os.environ, 'LEAN_NUM_THREADS': '1', 'LEAN_PATH': str(cache)},
                                       preexec_fn=bounds, start_new_session=True)
                while job.poll() is None:
                    minimum = min(minimum, available())
                    if minimum < RESERVE or time.monotonic() - started > BUDGET:
                        reason = 'reserve' if minimum < RESERVE else 'timeout'
                        os.killpg(job.pid, signal.SIGKILL)
                        break
                    time.sleep(.1)
                code = job.wait()
            record = dict(module=module, command=command, exit_code=code, stop_reason=reason,
                          seconds=round(time.monotonic()-started, 3), min_available_bytes=minimum,
                          source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(), log=str(log_path))
            record['log_sha256'] = hashlib.sha256(log_path.read_bytes()).hexdigest()
            records.append(record)
            (evidence / 'results.json').write_text(json.dumps(records, indent=2)+'\n')
            print(json.dumps(record), flush=True)
            if code != 0 or reason is not None:
                raise SystemExit(1)
        # The inventory is outside the library/core; Lean's toolchain supplies Lean.
        source = ROOT / args.controls
        if not source.resolve().is_relative_to(ROOT / 'tests/h55/g49-final-theorem'):
            raise ValueError('controls must be in the assigned helper directory')
        command = [str(args.lean.resolve()), '-j1', '--tstack=131072', str(source.relative_to(ROOT))]
        if available() < RESERVE:
            raise SystemExit('4 GiB reserve unavailable: no inventory job started')
        started, reason, minimum = time.monotonic(), None, available()
        with (evidence / 'controls.log').open('w') as log:
            job = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                   env={**os.environ, 'LEAN_NUM_THREADS': '1', 'LEAN_PATH': str(cache)},
                                   preexec_fn=bounds, start_new_session=True)
            while job.poll() is None:
                minimum = min(minimum, available())
                if minimum < RESERVE or time.monotonic() - started > BUDGET:
                    reason = 'reserve' if minimum < RESERVE else 'timeout'
                    os.killpg(job.pid, signal.SIGKILL)
                    break
                time.sleep(.1)
            code = job.wait()
        records.append(dict(module='H64Controls', command=command, exit_code=code,
                            stop_reason=reason, seconds=round(time.monotonic()-started, 3),
                            min_available_bytes=minimum,
                            source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                            log=str(evidence / 'controls.log'),
                            log_sha256=hashlib.sha256((evidence/'controls.log').read_bytes()).hexdigest()))
        (evidence / 'results.json').write_text(json.dumps(records, indent=2)+'\n')
        if code != 0 or reason is not None:
            raise SystemExit(1)
        (evidence / 'run-status.json').write_text(json.dumps(dict(
            status='pass', resultsSha256=hashlib.sha256((evidence/'results.json').read_bytes()).hexdigest()))+'\n')
        print('H64_SOURCE_AND_CONTROLS_CHECK_PASS', flush=True)


if __name__ == '__main__':
    main()
