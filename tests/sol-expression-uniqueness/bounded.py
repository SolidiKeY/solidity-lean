#!/usr/bin/env python3
"""Owned Docker run with writer lock, unchanged hard limits and H1 reserve guard."""
import fcntl, json, os, subprocess, sys, time, uuid
from pathlib import Path
root = Path(__file__).resolve().parents[2]
os.chdir(root)
name, *command = sys.argv[1:]
assert name and '/' not in name and command
out = root/'tests/sol-expression-uniqueness/evidence'
out.mkdir(exist_ok=True)
lockdir = Path('/tmp/solidity-lean-feature-groups-20261025')
lockdir.mkdir(exist_ok=True)
lock = (lockdir/'writer.lock').open('a')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
container = 'sol-eu-' + uuid.uuid4().hex[:12]
docker = ['env', '-u', 'DOCKER_HOST', '-u', 'DOCKER_CONTEXT', '-u', 'DOCKER_TLS',
          '-u', 'DOCKER_TLS_VERIFY', '-u', 'DOCKER_CERT_PATH',
          'docker', '--host=unix:///var/run/docker.sock']
image = 'ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852'
setup = ('set -eu; source /workspace/.setup/activate.sh; export LEAN_NUM_THREADS=1; '
         'export PATH=/workspace/solidity-lean/tests/sol-expression-uniqueness/runtime-bin:$PATH; '
         'export LEAN_MCP_SERVER_CMD="bash /workspace/solidity-lean/tests/sol-expression-uniqueness/runtime-mcp.sh"; '
         'exec python3 tests/sol-expression-uniqueness/inside.py "$@"')
args = docker + ['run', '--rm', '--name', container, '--memory=12g', '--memory-swap=12g',
                 '--cpus=1', '--user=1000:1000', '-v', '/workspace:/workspace',
                 '-v', '/opt:/opt:ro', '-v', '/usr:/usr:ro', '-w', str(root),
                 image, 'bash', '-c', setup, 'sol-eu', name] + command
reserve = 4 * 1024**3

def headroom():
    current = int(Path('/sys/fs/cgroup/memory.current').read_text())
    maximum = int(Path('/sys/fs/cgroup/memory.max').read_text())
    values = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
    available = int(values['MemAvailable'].split()[0]) * 1024
    return min(maximum-current, available)

minimum = headroom()
assert minimum >= reserve, 'H1 reserve unavailable before launch'
start = time.monotonic()
resource_stop = False
with (out/(name+'.log')).open('wb') as log:
    p = subprocess.Popen(args, stdout=log, stderr=subprocess.STDOUT)
    try:
        while p.poll() is None:
            minimum = min(minimum, headroom())
            if minimum < reserve:
                resource_stop = True
                subprocess.run(docker+['kill', container], stdout=log, stderr=log)
                break
            time.sleep(0.5)
        code = p.wait()
    except BaseException:
        subprocess.run(docker+['kill', container], stdout=log, stderr=log)
        p.wait()
        raise
result = dict(command=args, exit=code, wall_seconds=time.monotonic()-start,
              minimum_parent_headroom_bytes=minimum, required_reserve_bytes=reserve,
              resource_stop=resource_stop)
(out/(name+'.outer.json')).write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result), flush=True)
sys.exit(125 if resource_stop else code)
