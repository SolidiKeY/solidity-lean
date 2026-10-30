#!/usr/bin/env python3
"""Serial V08 import-closure gate in the managed local Docker daemon.
No network, fixed image, aggregate 12 GiB/no-swap cgroup, Lean -j1.
Writes logs and measured aggregate RSS; leaves containers for inspection.
"""
import fcntl, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
root = Path(__file__).resolve().parent.parent
requested = sys.argv[1:]
baseline = bool(requested and requested[0] == '--baseline')
if baseline:
 root = Path('/workspace/v08-baseline-pinned')
 requested = requested[1:]
sort_only = requested == ['--sort']
if sort_only: requested = ['SolkeyCheck']
full = requested == ['--full']
if full: requested = ['Solidity', 'SolkeyCheck', 'SolidityLean', 'SolkeyTestSuite']
evidence = Path('/workspace/v08-world-lowering-evidence')
evidence.mkdir(exist_ok=True)
lock = open('/tmp/solidity-lean-feature-groups-20261025/writer.lock', 'a')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
subprocess.run(['git', 'status', '--short'], cwd=root, check=True)
subprocess.run(['git', 'merge-base', '--is-ancestor',
 'fb379ae20f10e2c92113453ddd9d40d8f2efbe09', 'HEAD'], cwd=root, check=True)
if baseline:
 baseline_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
 if baseline_head != 'fb379ae20f10e2c92113453ddd9d40d8f2efbe09':
  raise SystemExit('Baseline checkout is not the exact pinned revision')
ordered, seen = [], set()
def visit(module):
 if module in seen: return
 seen.add(module)
 source = root / (module.replace('.', '/') + '.lean')
 if not source.exists(): return
 for line in source.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():
    if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', dep): visit(dep)
 ordered.append(module)
for target in requested:
 if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', target) or not (root / (target.replace('.', '/') + '.lean')).is_file():
  raise SystemExit('Missing or invalid explicit target: ' + target)
 visit(target)
if not ordered: raise SystemExit('Supply existing module targets')
config = root / 'scripts/v08-runtime.toml'
blocks = re.split(r'(?=\[\[)', (root / 'lakefile.toml').read_text())
for index, block in enumerate(blocks):
 if block.startswith('[[lean_lib]]') or block.startswith('[[lean_exe]]'):
  if 'weakLeanArgs' in block:
   blocks[index] = block.replace('weakLeanArgs = ["--tstack=131072"]', 'weakLeanArgs = ["--tstack=131072", "-j1"]')
  else:
   blocks[index] = block.rstrip() + '\nweakLeanArgs = ["-j1"]\n\n'
expected = ''.join(blocks).rstrip() + '\n'
if config.exists() and config.read_text() != expected:
 raise SystemExit('Unexpected alternate config: preserve and inspect')
config.write_text(expected)
env = os.environ.copy()
for key in ['DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH']:
 env.pop(key, None)
docker = ['docker', '--host=unix:///var/run/docker.sock']
name = 'v08-gate-' + str(os.getpid())
script = "export PATH=/opt/node:/opt/lean/bin:$PATH; set -eu; trap 'printf V08_CGROUP_PEAK=; cat /sys/fs/cgroup/memory.peak' EXIT; "
script += 'test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888; '
script += 'test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0; '
if full: script += 'node scripts/check-layers.mjs; '
for module in ordered:
 script += 'lake -f scripts/v08-runtime.toml build ' + module + '; '

cmd = docker + ['run', '--name', name, '--network', 'none', '--memory', '12g',
 '--memory-swap', '12g', '--cpus', '1', '--user', str(os.getuid()) + ':' + str(os.getgid()),
 '--mount', 'type=bind,src=' + str(root) + ',dst=' + str(root),
 '--mount', 'type=bind,src=/workspace/.setup/tools/lean-4.24.0-linux,dst=/opt/lean,readonly',
 '--mount', 'type=bind,src=/workspace/.setup/cache/lake,dst=/workspace/.setup/cache/lake',
 '--mount', 'type=bind,src=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin,dst=/opt/node,readonly',
 '--mount', 'type=bind,src=/workspace/.setup/solkey,dst=/workspace/.setup/solkey,readonly',
 '-w', str(root), '-e', 'LEAN_NUM_THREADS=1', '-e', 'LAKE_CACHE_DIR=/workspace/.setup/cache/lake',
 'ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852',
 'sh', '-c', script]
if full:
 script += 'lake -f scripts/v08-runtime.toml build; '
 script += 'lake -f scripts/v08-runtime.toml build SolkeyTestSuite; '
if full or sort_only:
 script += 'lake -f scripts/v08-runtime.toml exe solkeycheck --key ' + str(root / 'tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key') + '; '
# Refresh the final command after constructing the full-gate suffix.
cmd[-1] = script
logpath = evidence / (name + '.log')
peak = 0
samples = 0
guard_stopped = False
wall_limit_seconds = 600  # Conservative lane gate cap; no proof/test budget raised.
def fingerprint():
 paths = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard', '*.lean', 'lakefile.toml', 'scripts/v08-runtime.toml'], cwd=root).decode().split('\0')
 return {path: hashlib.sha256((root/path).read_bytes()).hexdigest() for path in sorted(set(paths)) if path and (root/path).is_file()}
source_before = fingerprint()
checked_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
started = time.monotonic()
with logpath.open('w') as log:
 log.write('$ ' + json.dumps(cmd) + '\n'); log.flush()
 proc = subprocess.Popen(cmd, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
 while proc.poll() is None:
  try:
   top = subprocess.run(docker + ['top', name, '-eo', 'pid,rss'], env=env,
    text=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, timeout=5)
  except subprocess.TimeoutExpired:
   guard_stopped = True
   log.write('DOCKER_TOP_TIMEOUT\n'); log.flush()
   subprocess.run(docker + ['stop', name], env=env, stdout=log, stderr=subprocess.STDOUT, timeout=15)
   break
  if top.returncode == 0:
   rss = sum(int(line.split()[1]) * 1024 for line in top.stdout.splitlines()[1:] if len(line.split()) == 2)
   peak = max(peak, rss); samples += 1
  available = int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))) * 1024
  if available < 2 * 1024**3 or peak > 12 * 1024**3 or time.monotonic() - started > wall_limit_seconds:
   guard_stopped = True
   log.write('RESOURCE_OR_TIME_GUARD_STOP\n'); log.flush()
   subprocess.run(docker + ['stop', name], env=env, stdout=log, stderr=subprocess.STDOUT, timeout=15)
  time.sleep(0.5)
 rc = proc.wait()
 if guard_stopped or samples == 0:
  rc = 125
 log.write('exit=' + str(rc) + '\n')
peak_match = re.search(r'^V08_CGROUP_PEAK=(\d+)$', logpath.read_text(), re.MULTILINE)
if rc == 0 and peak_match is None: rc = 125
source_after = fingerprint()
source_unchanged = source_after == source_before
if not source_unchanged: rc = 125
result = dict(command=cmd, modules=ordered, exit=rc, repository=str(root), full_gate=full, baseline=baseline,
 source_sha256=source_before, source_unchanged=source_unchanged, git_head_at_check=checked_head,
 log_sha256=hashlib.sha256(logpath.read_bytes()).hexdigest(),
 cgroup_peak_bytes=int(peak_match.group(1)) if peak_match else None,
 resource_or_time_guard_stopped=guard_stopped, wall_limit_seconds=wall_limit_seconds,
 peak_sampled_aggregate_rss_bytes=peak if samples else None,
 samples=samples, wall_seconds=time.monotonic()-started, log=str(logpath), container=name)
(evidence / (name + '.json')).write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['command','modules','source_sha256']}), flush=True)
print(logpath.read_text()[-5000:], flush=True)
raise SystemExit(rc)
