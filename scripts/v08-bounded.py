#!/usr/bin/env python3
"""Serial V08 import-closure gate in the managed local Docker daemon.
No network, fixed image, aggregate 12 GiB/no-swap cgroup, Lean -j1.
Writes logs and measured aggregate RSS; leaves containers for inspection.
"""
import fcntl, hashlib, importlib.util, json, os, re, signal, subprocess, sys, time, uuid
from pathlib import Path
root = Path(__file__).resolve().parent.parent
requested = sys.argv[1:]
baseline = bool(requested and requested[0] == '--baseline')
if baseline:
 root = Path('/workspace/v08-baseline-pinned')
 requested = requested[1:]
fresh_sort = requested == ['--fresh-sort']
if baseline and fresh_sort: raise SystemExit('Fresh executable gate is task-worktree only')
sort_only = requested == ['--sort'] or fresh_sort
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
def helper(name, filename):
 specification = importlib.util.spec_from_file_location(name, Path(__file__).parent/filename)
 module = importlib.util.module_from_spec(specification)
 sys.dont_write_bytecode = True
 specification.loader.exec_module(module)
 return module
build_graph = helper('v08_build_graph', 'v08-build-graph.py')
cleanup = helper('v08_cleanup', 'v08-container-cleanup.py')
graph = build_graph.SourceGraph(root)
ordered = graph.closure(requested)
if not ordered: raise SystemExit('Supply existing module targets')
native_modules = set(graph.closure(['SolkeyCheck'])) if full or sort_only else set()
if full: native_modules.update(graph.closure(['SolidityLean']))
assert native_modules <= set(ordered)
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
preflight = subprocess.run(docker + ['ps', '--filter', 'name=^/v08-gate-', '--format', '{{.Names}}'],
 env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=5)
if preflight.returncode != 0 or preflight.stdout.strip():
 (evidence/('v08-preflight-' + str(os.getpid()) + '.log')).write_text(
  'exit=' + str(preflight.returncode) + '\n' + preflight.stdout)
 raise SystemExit('Owned build may still be active or uninspectable; preserve it and inspect preflight evidence')
run_token = uuid.uuid4().hex
name = 'v08-gate-' + str(os.getpid()) + '-' + run_token[:8]
run_config = config
fresh = None
def digest_if_file(path):
 return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
if fresh_sort:
 fresh_dir = evidence / (name + '-fresh-output')
 run_config = evidence / (name + '-fresh.toml')
 if fresh_dir.exists() or run_config.exists():
  raise SystemExit('Fresh output/config already exists: preserve and inspect')
 fresh_text = expected.replace('version = "0.1.0"', 'version = "0.1.0"\nbuildDir = "' + str(fresh_dir) + '"', 1)
 # Validate that isolation changes only the supported output directory setting.
 import tomllib
 fresh_settings = tomllib.loads(fresh_text)
 assert fresh_settings.pop('buildDir') == str(fresh_dir)
 assert fresh_settings == tomllib.loads(expected)
 run_config.write_text(fresh_text)
 old_executable = root / '.lake/build/bin/solkeycheck'
 fresh = dict(directory=str(fresh_dir), initially_absent=True,
  original_executable=str(old_executable), original_sha256_before=digest_if_file(old_executable))
configuration_before = digest_if_file(run_config)
config_arg = str(run_config)
script = "export PATH=/opt/node:/opt/lean/bin:$PATH; set -eu; trap 'printf V08_CGROUP_PEAK=; cat /sys/fs/cgroup/memory.peak' EXIT; "
script += 'lean --version; lake --version; '
script += 'test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888; '
script += 'test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0; '
if full: script += 'node scripts/check-layers.mjs; '
for module in ordered:
 script += 'lake -f ' + config_arg + ' build ' + module + '; '
for module in ordered:
 if module in native_modules:
  script += 'lake -f ' + config_arg + ' build +' + module + ':c.o; '

cmd = docker + ['run', '--name', name, '--label', cleanup.LABEL + '=' + run_token, '--network', 'none', '--memory', '12g',
 '--memory-swap', '12g', '--cpus', '1', '--user', str(os.getuid()) + ':' + str(os.getgid()),
 '--mount', 'type=bind,src=' + str(root) + ',dst=' + str(root),
 '--mount', 'type=bind,src=/workspace/.setup/tools/lean-4.24.0-linux,dst=/opt/lean,readonly',
 '--mount', 'type=bind,src=/workspace/.setup/cache/lake,dst=/workspace/.setup/cache/lake',
 '--mount', 'type=bind,src=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin,dst=/opt/node,readonly',
 '--mount', 'type=bind,src=/workspace/.setup/solkey,dst=/workspace/.setup/solkey,readonly',
 *(['--mount', 'type=bind,src=' + str(evidence) + ',dst=' + str(evidence)] if fresh_sort else []),
 '-w', str(root), '-e', 'LEAN_NUM_THREADS=1', '-e', 'LAKE_CACHE_DIR=/workspace/.setup/cache/lake',
 'ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852',
 'sh', '-c', script]
if full:
 script += 'lake -f ' + config_arg + ' build; '
 script += 'lake -f ' + config_arg + ' build SolkeyTestSuite; '
if full or sort_only:
 script += 'lake -f ' + config_arg + ' exe solkeycheck --key ' + str(root / 'tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key') + '; '
# Refresh the final command after constructing the full-gate suffix.
cmd[-1] = script
logpath = evidence / (name + '.log')
peak = 0
samples = 0
guard_stopped = False
wall_limit_seconds = 600  # Conservative lane gate cap; no proof/test budget raised.
def fingerprint():
 paths = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard', '*.lean', 'lean-toolchain', 'lakefile.toml', 'scripts/v08-runtime.toml'], cwd=root).decode().split('\0')
 return {path: hashlib.sha256((root/path).read_bytes()).hexdigest() for path in sorted(set(paths)) if path and (root/path).is_file()}
source_before = fingerprint()
checked_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
started = time.monotonic()
def interrupted(number, _frame):
 raise RuntimeError('Build monitor interrupted by signal ' + str(number))
signal.signal(signal.SIGTERM, interrupted)
signal.signal(signal.SIGINT, interrupted)
monitor_error = None
cleanup_verified = False
with logpath.open('w') as log:
 log.write('$ ' + json.dumps(cmd) + '\n'); log.flush()
 proc = subprocess.Popen(cmd, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
 try:
  while proc.poll() is None:
   top = subprocess.run(docker + ['top', name, '-eo', 'pid,rss'], env=env,
    text=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, timeout=5)
   if top.returncode == 0:
    rss = sum(int(line.split()[1]) * 1024 for line in top.stdout.splitlines()[1:] if len(line.split()) == 2)
    peak = max(peak, rss); samples += 1
   available = int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))) * 1024
   if available < 2 * 1024**3 or peak > 12 * 1024**3 or time.monotonic() - started > wall_limit_seconds:
    guard_stopped = True
    log.write('RESOURCE_OR_TIME_GUARD_STOP\n'); log.flush()
    break
   time.sleep(0.5)
 except BaseException as error:
  guard_stopped = True
  monitor_error = type(error).__name__ + ': ' + str(error)
  log.write(monitor_error + '\n'); log.flush()
 finally:
  # Repeated interrupts must not abort ownership-verified bounded cleanup.
  signal.signal(signal.SIGTERM, signal.SIG_IGN)
  signal.signal(signal.SIGINT, signal.SIG_IGN)
  cleanup_verified, intervention = cleanup.ensure_stopped(docker, name, run_token, log, env=env)
  if intervention or not cleanup_verified: guard_stopped = True
  try:
   rc = proc.wait(timeout=5)
  except subprocess.TimeoutExpired:
   guard_stopped = True
   proc.terminate()  # Only the Docker client this script started.
   try: rc = proc.wait(timeout=5)
   except subprocess.TimeoutExpired:
    proc.kill()
    rc = proc.wait(timeout=5)
   # Recheck after cancelling a possibly pending Docker startup request.
   verified, _ = cleanup.ensure_stopped(docker, name, run_token, log, env=env)
   cleanup_verified = cleanup_verified and verified
 if guard_stopped or samples == 0 or not cleanup_verified: rc = 125
 log.write('exit=' + str(rc) + '\n')
peak_match = re.search(r'^V08_CGROUP_PEAK=(\d+)$', logpath.read_text(), re.MULTILINE)
if rc == 0 and peak_match is None: rc = 125
source_after = fingerprint()
source_unchanged = source_after == source_before
if not source_unchanged: rc = 125
configuration_unchanged = digest_if_file(run_config) == configuration_before
if not configuration_unchanged: rc = 125
version_lines = [line for line in logpath.read_text().splitlines() if line.startswith(('Lean (version ', 'Lake version '))]
if len(version_lines) != 2: rc = 125
if fresh is not None:
 fresh_executable = fresh_dir / 'bin/solkeycheck'
 fresh.update(executable=str(fresh_executable), executable_sha256=digest_if_file(fresh_executable),
  original_sha256_after=digest_if_file(old_executable))
 fresh['original_preserved'] = fresh['original_sha256_before'] == fresh['original_sha256_after']
 if rc == 0 and (not fresh['executable_sha256'] or not fresh['original_preserved']): rc = 125
result = dict(command=cmd, modules=ordered, exit=rc, repository=str(root), full_gate=full, baseline=baseline,
 monitor_error=monitor_error, container_cleanup_verified=cleanup_verified, run_token=run_token,
 module_sources={module: str(graph.source(module).relative_to(root)) for module in ordered},
 fresh_sort=fresh, native_modules=[module for module in ordered if module in native_modules],
 runtime_configuration=dict(path=str(run_config), sha256=configuration_before, unchanged=configuration_unchanged),
 tool_versions=version_lines, source_sha256=source_before, source_unchanged=source_unchanged, git_head_at_check=checked_head,
 log_sha256=hashlib.sha256(logpath.read_bytes()).hexdigest(),
 cgroup_peak_bytes=int(peak_match.group(1)) if peak_match else None,
 resource_or_time_guard_stopped=guard_stopped, wall_limit_seconds=wall_limit_seconds,
 peak_sampled_aggregate_rss_bytes=peak if samples else None,
 samples=samples, wall_seconds=time.monotonic()-started, log=str(logpath), container=name)
(evidence / (name + '.json')).write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['command','modules','source_sha256','module_sources']}), flush=True)
print(logpath.read_text()[-5000:], flush=True)
raise SystemExit(rc)
