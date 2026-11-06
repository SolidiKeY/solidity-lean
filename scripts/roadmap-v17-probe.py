#!/usr/bin/env python3
"""Bounded read-only baseline probes; never runs Lean, re-pins or repairs.

Run only from a committed clean V17 checkout. Output directory must be new.
Outputs retain failures and measured aggregate process-group RSS. These probes
are preparation, not the heavy G54 gates or runtime-keysort gate.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


def rss(group):
    total = 0
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit():
            continue
        try:
            stat = (entry / 'stat').read_text().rsplit(')', 1)[1].split()
            if int(stat[2]) == group:
                for line in (entry / 'status').read_text().splitlines():
                    if line.startswith('VmRSS:'):
                        total += int(line.split()[1]) * 1024
        except (OSError, ValueError, IndexError):
            pass
    return total


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--solkey-examples', type=Path, required=True)
    p.add_argument('--solkey-rules', type=Path, required=True)
    args = p.parse_args()
    lock_path = Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    writer_lock = lock_path.open('a+')
    try:
        fcntl.flock(writer_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        p.error('repository writer lock is held')
    root = Path(__file__).resolve().parents[1]
    revision = git(root, 'rev-parse', 'HEAD')
    if git(root, 'status', '--porcelain', '--untracked-files=all'):
        p.error('clean committed checkout required')
    args.out.mkdir(parents=True, exist_ok=False)
    inputs = {}
    paths = [args.solkey_rules, *args.solkey_examples.rglob('*.sol'), root / '.lake/build/bin/solkeycheck']
    for path in paths:
        if path.is_file(): inputs[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    commands = {
        'layers': ['node', 'scripts/check-layers.mjs'],
        'orphans': ['node', 'scripts/check-orphans.mjs'],
        'trust': ['bash', 'scripts/check-trust.sh'],
        'docs-full': ['bash', 'scripts/check-doc-paths.sh'],
        'testsuite-complete': ['bash', 'scripts/check-testsuite.sh', '--complete', '--solkey', str(args.solkey_examples)],
        'automatic-strict': ['node', 'scripts/check-automatic.mjs', '--strict'],
        'strict-correspondence': ['.lake/build/bin/solkeycheck', '--key', str(args.solkey_rules)],
        'g03-inventory': ['python3', '-I', 'scripts/roadmap-g03-ledger.py', '--check'],
        'public-import-inventory': ['node', 'scripts/roadmap-v17-imports.mjs'],
    }
    gates = []
    for name, command in commands.items():
        log = args.out / (name + '.log')
        start = time.monotonic()
        peak = 0
        with log.open('wb') as output:
            try:
                proc = subprocess.Popen(command, cwd=root, stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
                while proc.poll() is None:
                    peak = max(peak, rss(proc.pid))
                    if time.monotonic() - start > 60:
                        os.killpg(proc.pid, signal.SIGKILL)
                        proc.wait()
                        output.write(b'\nV17 probe timeout at 60s; failure retained.\n')
                        code = 124
                        break
                    time.sleep(0.05)
                else:
                    code = proc.returncode
            except OSError as error:
                output.write((str(error) + '\n').encode())
                code = 127
        gates.append({'id': name, 'revision': revision, 'command': command,
                      'exit': code, 'status': 'pass' if code == 0 else 'fail',
                      'log': log.name, 'sha256': hashlib.sha256(log.read_bytes()).hexdigest(),
                      'elapsedSeconds': round(time.monotonic() - start, 3), 'sampledAggregateRssBytes': peak})
    unchanged = git(root, 'rev-parse', 'HEAD') == revision and not git(root, 'status', '--porcelain', '--untracked-files=all')
    report = {'schema': 1, 'revision': revision, 'unchangedCheckout': unchanged,
              'releaseClosed': False, 'gates': gates, 'inputsSha256': inputs,
              'boundary': 'Read-only baseline probes; no new kernel, clean build, or cache-equivalence evidence.'}
    (args.out / 'gates.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'revision': revision, 'unchangedCheckout': unchanged,
                      'failed': [g['id'] for g in gates if g['exit'] != 0]}))
    return 0 if unchanged and all(g['exit'] == 0 for g in gates) else 1


if __name__ == '__main__':
    raise SystemExit(main())
