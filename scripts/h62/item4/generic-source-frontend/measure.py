#!/usr/bin/env python3
"""Matched serial warm-import proof comparison, stop if >10% slower.

Commands are exact JSON argument arrays, never shell strings. Each comparison
uses the same pinned compiler, source snapshot, object directory, -j1 and
bounds. Failures have no timing delta. This does not replace full final gates.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
from census import encode
from generate import REPO
from build_closure import LEAN, RUNTIME


def snapshot():
    paths = sorted((REPO/'Solidity').rglob('*.lean'))
    paths += sorted((REPO/'tests/h62/item4/generic-source-frontend').glob('*.lean'))
    return {str(p.relative_to(REPO)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--candidate', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--repetitions', type=int, default=3)
    args = ap.parse_args()
    if args.repetitions < 2:
        ap.error('at least two repetitions required')
    commands = {'baseline': json.loads(args.baseline.read_text()),
                'candidate': json.loads(args.candidate.read_text())}
    for command in commands.values():
        if not isinstance(command, list) or not all(isinstance(x, str) for x in command):
            ap.error('commands must be JSON string arrays')
        if not command or Path(command[0]).resolve() != LEAN.resolve() or '-j1' not in command or '--tstack=131072' not in command:
            ap.error('commands must use pinned Lean with explicit -j1 and stack')
        if '-o' in command or '-i' in command:
            ap.error('timed checks must not mutate import object artifacts')
    before = snapshot()
    for command in commands.values():
        for arg in command[1:]:
            if arg.endswith('.lean'):
                source = (REPO/arg).resolve()
                before[str(source)] = hashlib.sha256(source.read_bytes()).hexdigest()
    def unchanged_sources():
        now = snapshot()
        for key in before:
            if key.startswith('/'):
                now[key] = hashlib.sha256(Path(key).read_bytes()).hexdigest()
        return now == before
    env = dict(os.environ, LEAN_PATH=str(RUNTIME/'objects'), LEAN_NUM_THREADS='1')
    def object_snapshot():
        return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((RUNTIME/'objects').rglob('*.olean'))}
    objects = object_snapshot()
    records = []
    def save(status, delta=None):
        args.output.write_text(encode(dict(status=status, commands=commands,
            timings=records, delta_percent=delta,
            source_snapshot_sha256=hashlib.sha256(encode(before).encode()).hexdigest(),
            import_snapshot_sha256=hashlib.sha256(encode(objects).encode()).hexdigest(),
            resources='-j1, LEAN_NUM_THREADS=1, RLIMIT_AS12GiB, no swap, 4GiB reserve',
            cache='same isolated v4.35 warm imports; no old-master cache')))
    for repetition in range(args.repetitions):
        # Alternate order to reduce order bias under the same import snapshot.
        order = ['baseline', 'candidate'] if repetition % 2 == 0 else ['candidate', 'baseline']
        for label in order:
            log = args.output.with_name(args.output.stem + f'-{label}-{repetition}.log')
            code = subprocess.call([sys.executable, str(Path(__file__).with_name('bounded.py')),
                                    '--log', str(log), '--', *commands[label]], cwd=REPO, env=env)
            record = json.loads(Path(str(log)+'.json').read_text())
            record['label'] = label
            records.append(record)
            if code:
                save('BLOCKED_FAILED_CHECK')
                raise SystemExit(code)
            if not unchanged_sources() or object_snapshot() != objects:
                save('BLOCKED_INPUT_DRIFT')
                raise SystemExit('timing input drift')
        baseline = statistics.median(r['elapsed_seconds'] for r in records if r['label']=='baseline')
        candidate = statistics.median(r['elapsed_seconds'] for r in records if r['label']=='candidate')
        delta = (candidate/baseline-1)*100
        if delta > 10:
            save('STOP_SLOWDOWN_GT_10_PERCENT', delta)
            raise SystemExit('candidate exceeds 10% slowdown; no further checks')
    save('MATCHED_TIMING_PASS', delta)
    print(args.output.read_text())

if __name__ == '__main__':
    main()
