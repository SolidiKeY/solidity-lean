#!/usr/bin/env python3
"""Serial, source-bound standalone H55 gates; no production edits or full-gate claim."""
import fcntl, hashlib, importlib.util, json, os, pathlib, shlex, signal, subprocess, sys, time, tomllib, uuid

ROOT = pathlib.Path(__file__).resolve().parents[3]
OUT = pathlib.Path('/workspace/scratch/h55-interface-pairs/h82/evidence')
AREA = ROOT / 'tests/h55/interface-pairs'
CONFIG = AREA / 'runtime.toml'
IMAGE = 'ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852'
TARGETS = [
    'Solidity.Backend.Selection.PremisesV2',
    'Solidity.Backend.Selection.InterfaceV2Controls',
    'Solidity.Backend.MemoryCopies.Interface',
    'Solidity.Backend.MemoryCopies.InterfaceV2Laws',
    'Solidity.Backend.MemoryCopies.ControlsV2',
    'Solidity.Backend.Passes.MappedSequence',
    'Solidity.Backend.MemoryCopies.FixedPathCopyInterface',
    'Solidity.Backend.MemoryCopies.MemoryPathCopyInterface',
    'Solidity.Backend.MemoryCopies.FixedPathCopy',
    'Solidity.Backend.MemoryCopies.MemoryPathCopy',
    'Solidity.Backend.Passes.SharedPair',
]
LIMIT, RESERVE = 12 * 1024**3, 4 * 1024**3
MODE = sys.argv[1] if len(sys.argv) == 2 else ''
if MODE not in ('runtime', 'inputs', 'acceptance', 'baseline'):
    raise SystemExit('usage: bounded.py runtime|inputs|acceptance|baseline')
OUT.mkdir(parents=True, exist_ok=True)
pathlib.Path('/tmp/solidity-lean-feature-groups-20261025').mkdir(exist_ok=True)
lock = open('/tmp/solidity-lean-feature-groups-20261025/writer.lock', 'a')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
env = os.environ.copy()
for key in ('DOCKER_HOST', 'DOCKER_CONTEXT', 'DOCKER_TLS', 'DOCKER_TLS_VERIFY', 'DOCKER_CERT_PATH'):
    env.pop(key, None)
docker = ['docker', '--host=unix:///var/run/docker.sock']

def run(args, **kwargs):
    return subprocess.run(args, env=env, text=True, capture_output=True, timeout=15, **kwargs)

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

def available():
    host = int(next(line.split()[1] for line in pathlib.Path('/proc/meminfo').read_text().splitlines()
                    if line.startswith('MemAvailable:'))) * 1024
    cg = pathlib.Path('/sys/fs/cgroup')
    maximum = (cg / 'memory.max').read_text().strip()
    return host if maximum == 'max' else min(host, int(maximum) - int((cg / 'memory.current').read_text()))

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('h55_graph', ROOT / 'scripts/v08-build-graph.py')
graph_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(graph_module)
graph = graph_module.SourceGraph(ROOT)
modules = graph.closure(TARGETS)
assert modules and len(modules) == len(set(modules))
expected = (AREA / 'h82-input-modules.txt').read_text().splitlines()
assert expected == modules, 'stale input queue: regenerate census before checking'
settings = tomllib.loads(CONFIG.read_text())
for entry in settings.get('lean_lib', []) + settings.get('lean_exe', []):
    assert '-j1' in entry.get('weakLeanArgs', []), 'nonserial Lean configuration'
assert len(pathlib.Path('/proc/swaps').read_text().splitlines()) == 1, 'swap is active'
assert available() >= RESERVE, 'insufficient reserve'

paths = [graph.source(module) for module in modules]
paths += [ROOT / 'Solidity/Backend/MemoryCopies/InterfaceV2Roots.lean', ROOT / 'Solidity/KeySort.lean', ROOT / 'lean-toolchain',
          ROOT / 'lakefile.toml', ROOT / 'scripts/v08-build-graph.py']
paths += list((ROOT / 'scripts/h55/interface-pairs').glob('*.py'))
paths += [p for p in AREA.rglob('*') if p.is_file()]
# Imported artifact reuse is intentional. Bind each current artifact, to disclose
# the exact cache used by direct checks; KeySort itself has no imports.
artifacts = [ROOT / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')
             for m in modules]
paths = sorted(set(paths + [p for p in artifacts if p.is_file()]))
before = {str(p.relative_to(ROOT)): digest(p) for p in paths}
head = git('rev-parse', 'HEAD')
status = git('status', '--porcelain=v1')
name = 'h55-interface-' + uuid.uuid4().hex[:12]
log = OUT / (MODE + '-' + name + '.log')
q = shlex.quote
if MODE == 'inputs':
    command = '\n'.join(
        'printf "%s\\n" ' + q('H55_BEGIN=' + m) + '\n' +
        'lake -f tests/h55/interface-pairs/runtime.toml build ' + q('+' + m + ':olean') +
        '\nprintf "%s\\n" ' + q('H55_END=' + m) for m in modules)
elif MODE == 'baseline':
    baseline = [
        'Solidity/Backend/MemoryCopies/' + stem + '.lean'
        for stem in ('Interface', 'InterfaceV2', 'InterfaceV2Laws', 'InterfaceV2Roots')
    ] + [
        'Solidity/Backend/Selection/' + stem + '.lean'
        for stem in ('Interface', 'InterfaceV2', 'InterfaceV2Controls', 'Premises', 'PremisesV2')
    ]
    baseline += ['Solidity/Backend/Selection/FrameCapacityV2.lean', 'Solidity/Backend/MemoryCopies/FixedPathCopyInterface.lean', 'Solidity/Backend/MemoryCopies/MemoryPathCopyInterface.lean', 'Solidity/Backend/MemoryCopies/FixedPathCopy.lean', 'Solidity/Backend/MemoryCopies/MemoryPathCopy.lean', 'Solidity/Backend/Passes/SharedPair.lean']
    command = 'export LEAN_PATH=.lake/build/lib/lean\nTIMEFORMAT="H55_WALL_S=%R"\n'
    for path in baseline:
        for trial in range(1, 4):
            command += 'printf "%s\\n" ' + q('H55_TIMING=' + path + ':' + str(trial)) + '\n'
            command += 'time lean -j1 --tstack=131072 ' + q(path) + '\n'
    command += 'printf "%s\\n" H55_BASELINE_PASS'
elif MODE == 'acceptance':
    command = 'export LEAN_PATH=.lake/build/lib/lean\nlean -j1 --tstack=131072 tests/h55/interface-pairs/EquivalenceControls.lean\nprintf "%s\\n" H55_ACCEPTANCE_PASS'
else:
    command = 'lean --version\nlake --version\nexport LEAN_PATH=.lake/build/lib/lean\nlean -j1 --tstack=131072 Solidity/KeySort.lean\nprintf "%s\\n" H55_RUNTIME_PREREQUISITE_PASS'
script = 'exec 2>&1\nexport PATH=/opt/lean/bin:$PATH\n' + (
    'test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888\n'
    'test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0\n'
    'trap \'printf "H55_CGROUP_PEAK="; cat /sys/fs/cgroup/memory.peak\' EXIT\n') + command
cmd = docker + ['run', '--name', name, '--network', 'none', '--memory', '12g',
    '--memory-swap', '12g', '--cpus', '1', '--user', '1000:1000',
    '--mount', f'type=bind,src={ROOT},dst={ROOT}',
    '--mount', 'type=bind,src=/workspace/.setup/tools/lean-4.24.0-linux,dst=/opt/lean,readonly',
    '--mount', 'type=bind,src=/workspace/.setup/cache/lake,dst=/workspace/.setup/cache/lake',
    '-w', str(ROOT), '-e', 'LEAN_NUM_THREADS=1', '-e', 'XDG_CACHE_HOME=/workspace/.setup/cache',
    IMAGE, 'bash', '-euo', 'pipefail', '-c', script]
started = time.monotonic()
minimum, peak_rss, max_lean, samples = available(), 0, 0, 0
error = None
proc = None
info = None
cleanup = []

def interrupted(signum, frame):
    raise InterruptedError('signal ' + str(signum))

for sig in (signal.SIGINT, signal.SIGTERM):
    signal.signal(sig, interrupted)

def sample():
    global peak_rss, max_lean, samples
    result = run(docker + ['top', name, '-eo', 'pid,comm,rss,args'])
    if result.returncode:
        inspected = run(docker + ['inspect', name])
        if inspected.returncode:
            assert time.monotonic() - started < 5, 'container inspection unavailable'
            return
        state = json.loads(inspected.stdout)[0]['State']
        assert not state['Running'], 'cannot sample a live container'
        return
    rows = [line.split(None, 3) for line in result.stdout.splitlines()[1:]]
    owned = {int(row[0]) for row in rows}
    lean = []
    for row in rows:
        if row[1] != 'lean':
            continue
        task = pathlib.Path('/proc') / row[0]
        try:
            state = next(line for line in (task / 'status').read_text().splitlines()
                         if line.startswith('State:'))
            if state.split()[1] in ('Z', 'X'):
                continue
            args = (task / 'cmdline').read_bytes().split(b'\0')
            if b'-j1' not in args:
                state = next(line for line in (task / 'status').read_text().splitlines()
                             if line.startswith('State:'))
                if state.split()[1] in ('Z', 'X'):
                    continue
                raise AssertionError('live Lean command lacks explicit -j1: ' + repr(row) + ' ' + state)
        except FileNotFoundError:
            continue
        lean.append(row)
    assert len(lean) <= 1, 'multiple simultaneous live Lean jobs'
    peak_rss = max(peak_rss, sum(int(row[2]) * 1024 for row in rows))
    max_lean = max(max_lean, len(lean))
    samples += 1
    for p in pathlib.Path('/proc').iterdir():
        if not p.name.isdigit() or int(p.name) in owned:
            continue
        try:
            comm = (p / 'comm').read_text().strip()
            if comm not in ('lean', 'lake'):
                continue
            # A new owned process can appear after docker top. Its cgroup
            # identity establishes ownership without trusting a stale PID set.
            cgroup = (p / 'cgroup').read_text()
            cid = run(docker + ['inspect', '--format', '{{.Id}}', name]).stdout.strip()
            assert cid and cid in cgroup, 'competing external Lean/Lake process'
        except FileNotFoundError:
            continue

with log.open('w') as output:
    output.write(json.dumps(cmd) + '\n')
    output.flush()
    try:
        proc = subprocess.Popen(cmd, env=env, stdout=output, stderr=subprocess.STDOUT)
        while proc.poll() is None:
            minimum = min(minimum, available())
            assert minimum >= RESERVE, '4GiB headroom guard'
            assert time.monotonic() - started < 3600, '3600s runtime guard'
            sample()
            time.sleep(.5)
        code = proc.wait(timeout=15)
    except BaseException as exc:
        error = repr(exc)
        code = None
    finally:
        if error:
            signal.signal(signal.SIGINT, signal.SIG_IGN)
            signal.signal(signal.SIGTERM, signal.SIG_IGN)
            must_kill = True
            try:
                stopped = run(docker + ['stop', '-t', '5', name])
                cleanup.append(dict(action='stop', exit=stopped.returncode, stderr=stopped.stderr))
                must_kill = stopped.returncode != 0
            except BaseException as exc:
                cleanup.append(dict(action='stop', error=repr(exc)))
            if must_kill:
                try:
                    killed = run(docker + ['kill', name])
                    cleanup.append(dict(action='kill', exit=killed.returncode, stderr=killed.stderr))
                except BaseException as exc:
                    cleanup.append(dict(action='kill', error=repr(exc)))
        if proc is not None:
            try:
                code = proc.wait(timeout=20)
            except subprocess.TimeoutExpired:
                proc.kill()
                code = proc.wait(timeout=5)
                error = error or 'docker client failed to exit after cleanup'
        try:
            inspected = run(docker + ['inspect', name])
            assert inspected.returncode == 0, inspected.stderr
            info = json.loads(inspected.stdout)[0]
        except BaseException as exc:
            error = error or repr(exc)

after = {str(p.relative_to(ROOT)): digest(p) for p in paths if p.is_file()}
# Input builds are allowed to create/replace artifacts; sources/config/tooling
# may never change. Direct checks must preserve artifacts too.
stable = all(after.get(p) == h for p, h in before.items()
             if MODE != 'inputs' or not p.startswith('.lake/'))
stable = stable and git('rev-parse', 'HEAD') == head
if not stable:
    error = error or 'checked sources/configuration changed'
text = log.read_text()
if info:
    valid = (info['HostConfig']['Memory'] == LIMIT and info['HostConfig']['MemorySwap'] == LIMIT
             and not info['State']['OOMKilled'] and not info['State']['Running']
             and info['State']['ExitCode'] == 0)
    if not valid:
        error = error or 'container exit/resource validation failed'
if MODE == 'inputs':
    starts = [line.removeprefix('H55_BEGIN=') for line in text.splitlines() if line.startswith('H55_BEGIN=')]
    ends = [line.removeprefix('H55_END=') for line in text.splitlines() if line.startswith('H55_END=')]
    if starts != modules or ends != modules:
        error = error or 'incomplete exact module queue'
else:
    if MODE == 'baseline':
        import re
        timings = re.findall(r'^H55_TIMING=(.+)$', text, re.M)
        expected_timings = [path + ':' + str(trial) for path in baseline for trial in range(1, 4)]
        walls = re.findall(r'^H55_WALL_S=([0-9.]+)$', text, re.M)
        if timings != expected_timings or len(walls) != len(expected_timings):
            error = error or 'incomplete exact timing records'
    marker = {'acceptance': 'H55_ACCEPTANCE_PASS', 'baseline': 'H55_BASELINE_PASS', 'runtime': 'H55_RUNTIME_PREREQUISITE_PASS'}[MODE]
    if marker not in text.splitlines():
        error = error or 'missing completion marker'
if samples == 0:
    error = error or 'no successful process samples'
receipt = dict(mode=MODE, head=head, initial_status=status, command=cmd, exit=code,
    error=error, elapsed_s=time.monotonic()-started, minimum_headroom_bytes=minimum,
    sampled_peak_rss_bytes=peak_rss, max_sampled_lean_processes=max_lean, samples=samples,
    source_and_artifact_hashes_before=before, source_and_artifact_hashes_after=after,
    inputs_unchanged=stable, log=str(log), cleanup=cleanup,
    image_id=info['Image'] if info else None,
    container_state=info['State'] if info else None,
    limits=dict(memory=LIMIT, swap=0, reserve=RESERVE, threads=1))
log.with_suffix('.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if not k.startswith('source_and_artifact') and k != 'command'}))
raise SystemExit(1 if error or code != 0 else 0)
