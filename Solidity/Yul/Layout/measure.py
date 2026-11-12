#!/usr/bin/env python3
"""Serial, uncached source-elaboration measurements for the additive layout pilot.

Run from the checkout after warming prerequisite imports with the pinned toolchain.
Output must be outside the checkout. The driver warms every listed workload once,
then alternates baseline/candidate order. Shared modules are always charged before
candidate modules. Declaration pairs must be isolated proof bodies in files with
identical imports; their diagnostic timings are reported separately from modules.
The driver reports observations, never an automatic rollout acceptance verdict.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import signal
import statistics
import subprocess
import time
import threading


def imports(path):
    # Strip Lean's nested comments before parsing the import header. Reject
    # unsupported header syntax rather than silently losing a dependency.
    source = path.read_text()
    clean, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            clean.append(' ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            clean.append(source[i] if not depth or source[i] == '\n' else ' ')
            i += 1
    result = []
    for line in ''.join(clean).splitlines():
        tokens = line.split()
        if not tokens:
            continue
        if tokens[0] in {'prelude', 'module'} or (tokens[0] in {'public', 'meta'} and 'import' in tokens):
            raise ValueError(f'unsupported module header in {path}: {line}')
        if tokens[0] != 'import':
            break
        names = tokens[1:]
        if len(names) != 1 or any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', name) for name in names):
            raise ValueError(f'unsupported import syntax in {path}: {line}')
        result.extend(names)
    return result


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as source:
        for block in iter(lambda: source.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def manifest(root, files):
    pending = list(files)
    result = {}
    while pending:
        p = pending.pop().resolve()
        if str(p) in result:
            continue
        result[str(p)] = {'sha256': digest(p), 'lines': len(p.read_bytes().splitlines())}
        for name in imports(p):
            dep = root / (name.replace('.', '/') + '.lean')
            if dep.is_file():
                pending.append(dep)
            artifact = root / '.lake/build/lib/lean' / (name.replace('.', '/') + '.olean')
            if artifact.is_file() and str(artifact) not in result:
                result[str(artifact)] = {'sha256': digest(artifact)}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--baseline', action='append', default=[], metavar='FILE', help='baseline module (repeatable; defaults to ScalarWriteback)')
    parser.add_argument('--candidate', action='append', default=[], metavar='FILE', help='candidate instance module (repeatable)')
    parser.add_argument('--shared', action='append', default=[], metavar='FILE', help='new shared-core module, charged separately and in candidate totals')
    parser.add_argument('--declaration-pair', nargs=2, action='append', default=[], metavar=('OLD', 'NEW'), help='isolated declarations with identical imports; instrumentation reported separately')
    parser.add_argument('--baseline-only', action='store_true', help='collect a baseline without claiming a comparison')
    parser.add_argument('--runs', type=int, default=3, help='paired measured runs after warming (minimum 3)')
    parser.add_argument('--output', type=Path, required=True, help='new evidence directory outside the checkout')
    parser.add_argument('--timeout', type=int, default=600, help='per-file timeout in seconds; failure is retained')
    parser.add_argument('--memory-mib', type=int, default=12288, help='per-process virtual-memory ceiling, at most 12288 MiB')
    parser.add_argument('--cloud-vm', action='store_true', help='explicit H232 opt-in: VM isolation instead of a systemd scope; no swap required')
    args = parser.parse_args()
    root = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip()).resolve()
    if args.runs < 3 or not 0 < args.memory_mib <= 12288 or args.timeout <= 0:
        parser.error('require at least three runs, positive timeout and memory ceiling at most 12288 MiB')
    if not args.cloud_vm:
        parser.error('this driver requires explicit --cloud-vm for the H232 cloud execution path')
    if len(Path('/proc/swaps').read_text().splitlines()) != 1:
        parser.error('swap must be disabled')
    if not args.candidate and not args.baseline_only:
        parser.error('provide --candidate or explicitly select --baseline-only')
    if args.baseline_only and (args.candidate or args.shared or args.declaration_pair):
        parser.error('--baseline-only cannot include candidate/shared/declaration workloads')
    output = args.output.resolve()
    if output.is_relative_to(root):
        parser.error('evidence must be outside the checkout')
    groups = {
        'baseline': args.baseline or ['Solidity/Yul/Views/ScalarWriteback.lean'],
        'shared': args.shared,
        'candidate': args.candidate,
    }
    for i, pair in enumerate(args.declaration_pair):
        if imports(Path(pair[0])) != imports(Path(pair[1])):
            parser.error(f'declaration pair {i} has different imports')
        groups[f'declaration-{i}-old'] = [pair[0]]
        groups[f'declaration-{i}-new'] = [pair[1]]
    groups = {g: [str(Path(p).resolve()) for p in paths] for g, paths in groups.items()}
    for group, paths in groups.items():
        if len(paths) != len(set(str(Path(p).resolve()) for p in paths)):
            parser.error(f'duplicate workloads in {group}')
    files = [Path(p).resolve() for paths in groups.values() for p in paths]
    if any(not p.is_file() or p.suffix != '.lean' for p in files):
        parser.error('all workloads must be existing Lean source files')
    charged = [Path(p).resolve() for group in ['shared', 'candidate'] for p in groups[group]]
    if len(charged) != len(set(charged)):
        parser.error('shared and candidate modules must be charged exactly once')
    lock_path = Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    lock = lock_path.open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    closure = manifest(root, files)
    missing = [p for p in closure if p.endswith('.lean') and Path(p).is_relative_to(root / 'Solidity/Yul/Layout') and Path(p) not in charged]
    if missing and not args.baseline_only:
        parser.error('unaccounted Layout dependencies: ' + ', '.join(missing))
    output.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    report = {
        'schema': 1, 'root': str(root), 'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'cache_environment': {k: os.environ.get(k) for k in ['LAKE_CACHE_DIR', 'XDG_CACHE_HOME']},
        'platform': platform.platform(), 'machine': platform.node(), 'groups': groups,
        'command_line': __import__('sys').argv, 'limits': {'virtual_memory_mib': args.memory_mib, 'timeout_s': args.timeout, 'threads': 1, 'swap': False},
        'isolation': 'no systemd scope on the cloud VM (H232)',
        'versions': {cmd: subprocess.check_output([cmd, '--version'], text=True).strip() for cmd in ['lean', 'lake']},
        'manifest': manifest(root, files), 'samples': [], 'status': 'running',
        'boundary': 'Source elaboration via guarded per-file checks; imports are cached. No rollout or proof acceptance inferred.',
    }

    def save():
        (output / 'result.json').write_text(json.dumps(report, indent=2) + '\n')

    def limit():
        ceiling = args.memory_mib * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (ceiling, ceiling))

    def run(group, path, phase, iteration):
        available = int(re.search(r'MemAvailable:\s+(\d+)', Path('/proc/meminfo').read_text()).group(1))
        if available < (args.memory_mib + 2048) * 1024:
            raise RuntimeError('insufficient available memory for ceiling plus 2 GiB OS reserve')
        directory = output / f'{len(report["samples"]):03d}'
        directory.mkdir()
        cmd = ['bash', 'scripts/coord-tools/gate.sh', 'per-file', path]
        start = time.perf_counter_ns()
        with (directory / 'stdout.log').open('wb') as log:
            process = subprocess.Popen(cmd, cwd=root, env=dict(env, GATE_LOGS=str(directory / 'gate')),
                                       stdout=log, stderr=subprocess.STDOUT, start_new_session=True, preexec_fn=limit)
            expired = threading.Event()
            def terminate():
                if process.returncode is None:
                    expired.set()
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            watchdog = threading.Timer(args.timeout, terminate)
            watchdog.start()
            interrupted = None
            try:
                _, status, usage = os.wait4(process.pid, 0)
                elapsed = time.perf_counter_ns() - start
                code = os.waitstatus_to_exitcode(status)
                process.returncode = code
            except BaseException as error:
                interrupted = error
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                _, status, usage = os.wait4(process.pid, 0)
                elapsed = time.perf_counter_ns() - start
                code = os.waitstatus_to_exitcode(status)
                process.returncode = code
            finally:
                watchdog.cancel()
                watchdog.join()
            timed_out = expired.is_set()
        peak = None if timed_out or interrupted else usage.ru_maxrss  # Linux KiB; killed descendants may not be reaped.
        gate_logs = list((directory / 'gate').glob('*.log'))
        retried = bool(list((directory / 'gate').glob('*.first'))) or any('RETRY-SIGBUS' in p.read_text(errors='replace') for p in gate_logs)
        rebuilt = any(re.search(r'\bBuilt\b', p.read_text(errors='replace')) for p in gate_logs)
        sample = {'group': group, 'file': path, 'phase': phase, 'iteration': iteration, 'command': cmd,
                  'elapsed_ns': elapsed, 'peak_rss_kib': peak, 'exit_code': code, 'timeout': timed_out, 'interrupted': repr(interrupted) if interrupted else None, 'retried': retried, 'rebuilt_imports': rebuilt, 'logs': str(directory)}
        report['samples'].append(sample)
        save()
        print(json.dumps(sample), flush=True)
        if interrupted:
            raise interrupted
        if code or timed_out or retried or (phase == 'measurement' and rebuilt):
            raise RuntimeError(f'failed elaboration retained in {directory}')

    save()
    try:
        for group, paths in groups.items():
            for path in paths:
                run(group, path, 'warmup', 0)
        for iteration in range(args.runs):
            order = ['baseline', 'shared', 'candidate'] if iteration % 2 == 0 else ['shared', 'candidate', 'baseline']
            declaration_groups = [g for g in groups if g.startswith('declaration-')]
            order += declaration_groups if iteration % 2 == 0 else list(reversed(declaration_groups))
            for group in order:
                for path in groups[group]:
                    run(group, path, 'measurement', iteration)
        report['manifest_after'] = manifest(root, files)
        if report['manifest_after'] != report['manifest']:
            raise RuntimeError('source or import artifacts changed during experiment')
        measured = [s for s in report['samples'] if s['phase'] == 'measurement']
        def summary(values):
            return {'median_ns': statistics.median(values), 'min_ns': min(values), 'max_ns': max(values)}
        report['per_module'] = {f'{g}:{p}': summary([s['elapsed_ns'] for s in measured if s['group'] == g and s['file'] == p])
                                for g, paths in groups.items() for p in paths}
        report['totals'] = {name: summary([sum(s['elapsed_ns'] for s in measured if s['iteration'] == i and s['group'] in selected)
                                         for i in range(args.runs)])
                            for name, selected in [('baseline', ['baseline']), ('shared', ['shared']), ('instances', ['candidate']),
                                                   ('candidate_including_shared', ['shared', 'candidate'])]}
        report['status'] = 'baseline-only' if args.baseline_only else 'measured; acceptance requires declaration/dependency review and uncertainty assessment'
    except BaseException as error:
        report['status'] = 'failed'
        report['error'] = str(error)
        raise
    finally:
        save()
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
