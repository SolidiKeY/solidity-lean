#!/usr/bin/env python3
"""Check one guard deletion on temporary copies; stop on low headroom."""
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import time

root = Path(__file__).resolve().parents[3]
source = root / 'Solidity/Yul/Adapters/RawPhysicalCalldata.lean'
guard = '  first | (simp only;done) | decide | omega | rfl | skip\n'
base = source.read_text()
assert base.count(guard) == 1
out = Path('/workspace/h55-proof-guards-evidence/calldata-probe')
out.mkdir(parents=True, exist_ok=True)
probe = out / 'RawPhysicalCalldata.lean'
lean = '/workspace/.setup/tools/lean-4.24.0-linux/bin/lean'
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
for label, data in [('before', base), ('after', base.replace(guard, ''))] * 3:
    probe.write_text(data)
    command = [lean, '-j1', '--tstack=131072', str(probe)]
    check_reserve()
    started = time.monotonic()
    p = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
    while True:
        try:
            output = p.communicate(timeout=0.02)[0].decode()
            break
        except subprocess.TimeoutExpired:
            available = int(next(line.split()[1] for line in open('/proc/meminfo') if line.startswith('MemAvailable:')))
            current = int(Path('/sys/fs/cgroup/memory.current').read_text())
            maximum = int(Path('/sys/fs/cgroup/memory.max').read_text())
            if available < 4194304 or maximum - current < 4294967296:
                p.terminate()
                p.communicate()
                raise SystemExit('RESOURCE STOP: less than 4 GiB reserve')
    elapsed = time.monotonic() - started
    rows.append({'case': label, 'seconds': elapsed, 'exit': p.returncode,
                 'source_sha256': hashlib.sha256(data.encode()).hexdigest(), 'output': output})
    print(label, round(elapsed, 4), 'exit', p.returncode, flush=True)
    if p.returncode:
        break
before = [r['seconds'] for r in rows if r['case'] == 'before']
after = [r['seconds'] for r in rows if r['case'] == 'after']
ratio = statistics.median(after) / statistics.median(before) if len(before) == len(after) == 3 else None
result = {'command': command, 'cwd': str(root), 'LEAN_PATH': str(lean_path), 'LEAN_NUM_THREADS': '1',
          'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'oleans_sha256': hashlib.sha256((out / 'oleans.json').read_bytes()).hexdigest(),
          'rows': rows, 'median_ratio': ratio,
          'status': 'pass' if ratio is not None and ratio <= 1.1 and all(r['exit'] == 0 for r in rows) else 'stop-or-fail'}
(out / 'results-timed.json').write_text(json.dumps(result, indent=2) + '\n')
print('median ratio:', ratio, 'status:', result['status'])
