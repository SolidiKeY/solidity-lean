#!/usr/bin/env python3
"""Owned serial Lean gates: 12 GiB/no swap, one CPU, effective 4 GiB reserve.
Bulk evidence is external. Only this invocation's container may be stopped.
"""
import fcntl, hashlib, importlib.util, json, os, pathlib, shlex, subprocess, sys, time, uuid
sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[3]
EVIDENCE = pathlib.Path('/workspace/v08-agreements-evidence')
IMAGE = 'ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852'
RESERVE = 4 * 1024**3

def reserve_snapshot():
    host = int(next(line.split()[1] for line in pathlib.Path('/proc/meminfo').read_text().splitlines()
                    if line.startswith('MemAvailable:'))) * 1024
    mount = pathlib.Path('/sys/fs/cgroup')
    relative = next(line.split(':', 2)[2] for line in pathlib.Path('/proc/self/cgroup').read_text().splitlines()
                    if line.startswith('0::'))
    current = mount / relative.lstrip('/')
    if not current.is_dir():
        raise RuntimeError('Cannot locate effective cgroup: ' + str(current))
    limits = []
    while current.is_relative_to(mount):
        cap_file = current / 'memory.max'
        if cap_file.is_file():
            cap = cap_file.read_text().strip()
            used = int((current / 'memory.current').read_text())
            if cap != 'max':
                limits.append(dict(path=str(current), cap=int(cap), current=used, available=int(cap)-used))
        if current == mount:
            break
        current = current.parent
    if not limits:
        raise RuntimeError('No finite outer cgroup memory limit observed')
    return dict(host_available=host, cgroups=limits,
                effective_available=min([host] + [item['available'] for item in limits]))

def fingerprint():
    names = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard',
                                     '*.lean', 'lean-toolchain', 'lakefile.toml'], cwd=ROOT).decode().split('\0')
    return {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
            for name in sorted(set(names)) if name and (ROOT/name).is_file()}

def main():
    label, *targets = sys.argv[1:]
    if not targets or pathlib.Path(label).name != label:
        raise SystemExit('label and module targets, or label --files FILE... required')
    EVIDENCE.mkdir(exist_ok=True)
    lock = open('/tmp/solidity-lean-feature-groups-20261025/writer.lock', 'a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    subprocess.run(['git', 'status', '--short'], cwd=ROOT, check=True)
    file_mode = targets[0] == '--files'
    files = targets[1:] if file_mode else []
    if file_mode and not files:
        raise SystemExit('No files requested')
    for file in files:
        path = (ROOT/file).resolve()
        if not path.is_relative_to(ROOT) or not path.is_file() or path.suffix != '.lean':
            raise SystemExit('Invalid source file: ' + file)
    spec = importlib.util.spec_from_file_location('graph', ROOT/'scripts/v08-build-graph.py')
    graph = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(graph)
    ordered = [] if file_mode else graph.SourceGraph(ROOT).closure(targets)
    config = ROOT/'scripts/h55/v08-agreements/runtime.toml'
    config.write_text((ROOT/'lakefile.toml').read_text().replace(
        'weakLeanArgs = ["--tstack=131072"]', 'weakLeanArgs = ["--tstack=131072", "-j1"]'))
    script = '''set -eu
export PATH=/opt/lean/bin:$PATH
lean --version
lake --version
test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888
test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0
trap 'printf H55_MEMORY_PEAK=; cat /sys/fs/cgroup/memory.peak; printf H55_SWAP_CURRENT=; cat /sys/fs/cgroup/memory.swap.current; echo H55_MEMORY_EVENTS; cat /sys/fs/cgroup/memory.events' EXIT
run_step() {
  tag=$1; shift; start=$(date +%s%N)
  set +e; "$@"; code=$?; set -e
  end=$(date +%s%N)
  printf 'H55_STEP %s %s %s\\n' "$tag" "$code" "$((end-start))"
  return "$code"
}
lean -j1 --tstack=131072 Solidity/KeySort.lean
echo KEYSORT_PASS
'''
    for module in ordered:
        script += 'run_step '+shlex.quote(module)+' lake -f '+shlex.quote(str(config))+' build '+shlex.quote(module)+'\n'
    for file in files:
        script += 'run_step '+shlex.quote(file)+' lake -f '+shlex.quote(str(config))+' env lean -j1 --tstack=131072 '+shlex.quote(file)+'\n'
    script += 'echo '+('FILE_CHECKS_PASS' if file_mode else 'AFFECTED_CLOSURE_PASS')+'\n'
    owner = uuid.uuid4().hex
    owner_label = 'io.openai.h55-v08-agreements.owner'
    name = 'h55-v08-agreements-' + owner
    env = os.environ.copy()
    for key in ['DOCKER_HOST', 'DOCKER_CONTEXT', 'DOCKER_TLS', 'DOCKER_TLS_VERIFY', 'DOCKER_CERT_PATH']:
        env.pop(key, None)
    docker = ['docker', '--host=unix:///var/run/docker.sock']
    cmd = docker + ['run', '--name', name, '--label', owner_label+'='+owner, '--network', 'none', '--memory', '12g', '--memory-swap', '12g',
                    '--cpus', '1', '--user', str(os.getuid())+':'+str(os.getgid()),
                    '--mount', 'type=bind,src='+str(ROOT)+',dst='+str(ROOT),
                    '--mount', 'type=bind,src=/workspace/.setup/tools/lean-4.24.0-linux,dst=/opt/lean,readonly',
                    '--mount', 'type=bind,src=/workspace/.setup/cache/lake,dst=/workspace/.setup/cache/lake',
                    '-w', str(ROOT), '-e', 'LEAN_NUM_THREADS=1', '-e', 'XDG_CACHE_HOME=/workspace/.setup/cache',
                    IMAGE, 'sh', '-c', script]
    def stop_owned():
        check = subprocess.run(docker+['inspect', '--format', '{{ index .Config.Labels "'+owner_label+'" }}', name],
                               env=env, capture_output=True, text=True)
        if check.returncode:
            raise RuntimeError('Cannot verify owned container before stop: '+name)
        if check.stdout.strip() != owner:
            raise RuntimeError('Container ownership mismatch; refusing stop: '+name)
        subprocess.run(docker+['stop', name], env=env, check=True)
    logpath = EVIDENCE/(label+'.log')
    if logpath.exists():
        raise SystemExit('Refusing to overwrite evidence: '+str(logpath))
    before = fingerprint()
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    samples = [dict(seconds=0, **reserve_snapshot())]
    if samples[0]['effective_available'] < RESERVE:
        raise SystemExit('Insufficient effective memory reserve before launch')
    started = time.monotonic()
    stopped = False
    with logpath.open('w') as log:
        log.write('$ '+shlex.join(cmd)+'\n'); log.flush()
        proc = subprocess.Popen(cmd, env=env, stdout=log, stderr=subprocess.STDOUT)
        try:
            while proc.poll() is None:
                snap = reserve_snapshot()
                stats = subprocess.run(docker+['stats', '--no-stream', '--format', '{{.MemUsage}}', name],
                                       env=env, capture_output=True, text=True)
                samples.append(dict(seconds=time.monotonic()-started, **snap,
                                    docker_stats=stats.stdout.strip(), stats_exit=stats.returncode))
                if snap['effective_available'] < RESERVE:
                    stopped = True
                    stop_owned()
                    break
                time.sleep(1)
        except BaseException:
            stop_owned()
            proc.wait()
            raise
        code = proc.wait()
    inspect = subprocess.run(docker+['inspect', '--format', '{{json .State}}', name],
                             env=env, capture_output=True, text=True)
    after = fingerprint()
    if before != after or inspect.returncode:
        code = 126
    result = dict(head=head, runner_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                  config_sha256=hashlib.sha256(config.read_bytes()).hexdigest(), source_before=before,
                  source_after=after, source_unchanged=before==after, samples=samples, command=cmd,
                  targets=targets, ordered=ordered, exit=code, guard_stopped=stopped,
                  seconds=time.monotonic()-started, container=name, owner_label=owner_label, owner_nonce=owner, state=inspect.stdout,
                  inspect_exit=inspect.returncode, log=str(logpath))
    (EVIDENCE/(label+'.json')).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ['exit', 'guard_stopped', 'seconds', 'container', 'log']}), flush=True)
    return 125 if stopped else code

if __name__ == '__main__':
    raise SystemExit(main())
