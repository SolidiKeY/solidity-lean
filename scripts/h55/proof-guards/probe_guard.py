#!/usr/bin/env python3
"""Check selected exact-form guard deletions in a tracked file using temporary copies."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', required=True, type=Path, help='new directory for probe evidence')
parser.add_argument('--source', required=True, type=Path, help='tracked Lean file relative to repository root')
parser.add_argument('--line', required=True, action='append', type=int, help='one-based exact candidate line; repeat to select multiple lines')
parser.add_argument('--lean', default=os.environ.get('LEAN', 'lean'), help='Lean executable (default: LEAN or lean on PATH)')
args = parser.parse_args()
lean = shutil.which(args.lean)
if lean is None:
    parser.error(f'Lean executable not found: {args.lean}')
lean = os.path.abspath(lean)
root = Path(__file__).resolve().parents[3]
version = subprocess.run([lean, '--version'], cwd=root, check=True, capture_output=True, text=True, timeout=30).stdout.strip()
lean_sha256 = hashlib.sha256(Path(lean).read_bytes()).hexdigest()

expected_version = (root / 'lean-toolchain').read_text().strip().rsplit(':v', 1)[-1]
if not version.startswith(f'Lean (version {expected_version},'):
    raise SystemExit(f'Lean version mismatch: expected {expected_version}; got {version}')
source = (root / args.source).resolve()
if not source.is_relative_to(root) or source.suffix != '.lean':
    raise SystemExit('source must be a Lean file inside the repository')
source_name = str(source.relative_to(root))
subprocess.run(['git', 'ls-files', '--error-unmatch', '--', source_name], cwd=root,
               check=True, stdout=subprocess.DEVNULL)
base = source.read_bytes().decode('utf-8')
lines = base.splitlines(keepends=True)
forms = {'first | (simp only;done) | decide | omega | rfl | skip',
         'first | (simp only;done) | (decide) | omega | rfl | skip'}
if len(set(args.line)) != len(args.line):
    raise SystemExit('duplicate candidate line')
if any(line < 1 or line > len(lines) or lines[line - 1].strip() not in forms for line in args.line):
    raise SystemExit('selected line is not an exact-form guard')
selected = set(args.line)
modified = ''.join(text for number, text in enumerate(lines, 1) if number not in selected)
out = args.output.resolve()
out.mkdir(parents=True, exist_ok=False)
probe = out / source.name
lean_path = root / '.lake/build/lib/lean'
env = os.environ.copy()
env.update(LEAN_NUM_THREADS='1', LEAN_PATH=str(lean_path))
artifacts = []
for path in sorted(lean_path.rglob('*.olean')):
    artifacts.append([str(path.relative_to(lean_path)), hashlib.sha256(path.read_bytes()).hexdigest()])
(out / 'oleans.json').write_text(json.dumps(artifacts, indent=2) + '\n')
def check_reserve():
    available = int(next(line.split()[1] for line in open('/proc/meminfo') if line.startswith('MemAvailable:')))
    current = int(Path('/sys/fs/cgroup/memory.current').read_text())
    maximum = int(Path('/sys/fs/cgroup/memory.max').read_text())
    if available < 4194304 or maximum - current < 4294967296:
        raise RuntimeError('RESOURCE STOP: less than 4 GiB reserve')


rows = []
pair_ratios = []
stop_reason = None
for label, data in [('before', base), ('after', modified)] * 3:
    probe.write_bytes(data.encode('utf-8'))
    command = [lean, '-j1', '--tstack=131072', str(probe)]
    check_reserve()
    started = time.monotonic()
    p = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
    try:
        while True:
            try:
                output = p.communicate(timeout=0.02)[0].decode()
                break
            except subprocess.TimeoutExpired:
                check_reserve()
    finally:
        if p.poll() is None:
            p.terminate()
            p.communicate()
    elapsed = time.monotonic() - started
    rows.append({'case': label, 'seconds': elapsed, 'exit': p.returncode,
                 'source_sha256': hashlib.sha256(data.encode()).hexdigest(), 'output': output})
    print(label, round(elapsed, 4), 'exit', p.returncode, flush=True)
    if p.returncode:
        stop_reason = 'Lean invocation failed'
        break
    if label == 'after':
        pair_ratio = elapsed / rows[-2]['seconds']
        pair_ratios.append(pair_ratio)
        if pair_ratio > 1.1:
            stop_reason = 'TIMING STOP: paired slowdown exceeds 10%'
            print(stop_reason, 'ratio:', pair_ratio, flush=True)
            break
before = [r['seconds'] for r in rows if r['case'] == 'before']
after = [r['seconds'] for r in rows if r['case'] == 'after']
ratio = statistics.median(after) / statistics.median(before) if len(before) == len(after) == 3 else None
if stop_reason is None and ratio is not None and ratio > 1.1:
    stop_reason = 'TIMING STOP: median slowdown exceeds 10%'
result = {'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
          'tracked_status': subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=root, text=True),
          'source': source_name, 'line': args.line[0] if len(args.line) == 1 else None,
          'lines': sorted(args.line), 'command': command, 'lean_version': version, 'lean_sha256': lean_sha256, 'cwd': str(root), 'LEAN_PATH': str(lean_path), 'LEAN_NUM_THREADS': '1',
          'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'oleans_sha256': hashlib.sha256((out / 'oleans.json').read_bytes()).hexdigest(),
          'rows': rows, 'pair_ratios': pair_ratios, 'stop_reason': stop_reason, 'median_ratio': ratio,
          'status': 'pass' if stop_reason is None and ratio is not None and ratio <= 1.1 and all(r['exit'] == 0 for r in rows) else 'stop-or-fail'}
(out / 'results-timed.json').write_text(json.dumps(result, indent=2) + '\n')
print('median ratio:', ratio, 'status:', result['status'])
if result['status'] != 'pass':
    raise SystemExit(1)
