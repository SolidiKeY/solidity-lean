#!/usr/bin/env python3
"""Serial Docker check runner with an outer-cgroup 4 GiB reserve guard.
Invoke under the repository writer lock. Measurements are external evidence.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

repo = Path(__file__).resolve().parents[3]
label, *command = sys.argv[1:]
if not command or not label.replace('-', '').replace('_', '').isalnum():
    raise SystemExit('usage: run-bounded.py LABEL COMMAND ARG...')
evidence = Path(__file__).resolve().parent / 'evidence'
name = 'control-tuples-' + str(os.getpid())
cg = Path('/sys/fs/cgroup')
reserve = 4 * 1024 ** 3

def headroom():
    available = int((cg / 'memory.max').read_text()) - int((cg / 'memory.current').read_text())
    host = next(int(s.split()[1]) * 1024 for s in Path('/proc/meminfo').read_text().splitlines()
                if s.startswith('MemAvailable:'))
    return min(available, host)

def measured_rss(suffixes):
    total = 0
    for p in Path('/proc').glob('[0-9]*'):
        try:
            executable = (p / 'cmdline').read_bytes().split(b'\0')[0]
            if executable.rsplit(b"/", 1)[-1] in {name.rsplit(b"/", 1)[-1] for name in suffixes}:
                total += int((p / 'statm').read_text().split()[1]) * os.sysconf('SC_PAGE_SIZE')
        except (OSError, ValueError, IndexError):
            pass
    return total

if headroom() < reserve:
    raise SystemExit('RESOURCE_STOP: less than 4 GiB available before launch')
docker = ['docker', '--host=unix:///var/run/docker.sock']
args = docker + ['run', '--rm', '--name', name, '--memory=12g', '--memory-swap=12g',
    '--cpus=1', '--user=1000:1000', '-v', '/workspace:/workspace', '-v', '/opt:/opt:ro',
    '-v', '/usr:/usr:ro', '-v', str(evidence / ('lakefile.runtime.toml' if os.environ.get('CONTROL_TUPLE_CONFIG') == 'runtime' else 'lakefile.serial.toml')) + ':' + str(repo / 'lakefile.toml') + ':ro',
    '-w', str(repo), 'ubuntu:24.04', 'bash', '-c',
    'set -eu; test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888; '
    'test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0; '
    'source /workspace/.setup/activate.sh; '
    'export LEAN_NUM_THREADS=1 LEAN_LSP_MAX_OPEN_FILES=1; exec "$@"', 'bounded-check'] + command
manifest = {str(p.relative_to(repo)): hashlib.sha256(p.read_bytes()).hexdigest()
    for p in sorted(list((repo / 'Solidity/Frontend/ExecutableAst/ControlTuple').glob('*.lean')) + list(Path(__file__).resolve().parent.glob('*.lean')) + list(Path(__file__).resolve().parent.glob('*.sol')) + list(Path(__file__).resolve().parent.glob('*.ast.json')))}
start = time.monotonic()
peak = 0
peak_check = 0
minimum = headroom()
stopped = False
with (evidence / (label + '.log')).open('w') as log:
    process = subprocess.Popen(args, stdout=log, stderr=subprocess.STDOUT)
    while process.poll() is None:
        peak = max(peak, measured_rss((b'/lean', b'/lake')))
        peak_check = max(peak_check, measured_rss((b'/lean', b'/lake', b'/clang', b'/ld.lld', b'/control-tuples-probe')))
        minimum = min(minimum, headroom())
        if minimum < reserve:
            subprocess.run(docker + ['stop', name], stdout=log, stderr=subprocess.STDOUT)
            stopped = True
            break
        time.sleep(0.5)
    result = process.wait()
record = {'command': command, 'docker_command': args, 'head': subprocess.check_output(
    ['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(), 'source_sha256': manifest,
    'exit': result, 'resource_stop': stopped, 'wall_s': round(time.monotonic() - start, 3),
    'peak_aggregate_lean_lake_rss_bytes': peak, 'peak_relevant_check_process_rss_bytes': peak_check, 'minimum_available_headroom_bytes': minimum,
    'memory_max': 12884901888, 'memory_swap_max': 0,
    'measurement': '0.5s sampled relevant process RSS across this VM; OS/cache and unlisted processes excluded'}
(evidence / (label + '.json')).write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
raise SystemExit(1 if stopped else result)
