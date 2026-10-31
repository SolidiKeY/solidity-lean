#!/usr/bin/env python3
"""V17 bounded build provenance. Consistency evidence, never kernel authentication."""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shlex
import subprocess
import time
import uuid
import re

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('v17_evidence', ROOT / 'scripts/roadmap-v17-evidence.py')
e = importlib.util.module_from_spec(spec)
spec.loader.exec_module(e)
rspec = importlib.util.spec_from_file_location('v17_resources', ROOT / 'scripts/roadmap-v17-resources.py')
resources = importlib.util.module_from_spec(rspec); rspec.loader.exec_module(resources)
resource_snapshot = resources.resource_snapshot
check_headroom = resources.check_headroom
UNRESOLVED = Path('/workspace/scratch/v17-unresolved-container.json')
CAP = resources.CAP
BUDGET = {'processSeconds': 300, 'suiteModuleSeconds': 300, 'leanNumThreads': 1}
SAMPLE_FORMAT = 'pid-stat-comm-rss-args/native-v2'
IMAGE = 'debian@sha256:99c0b25c46d0214d5a2091092e7908907dcaecd6a962cde0ac700acee222b6f3'
TARGETS = {
    'runtime-keysort': (['Solidity.KeySort'], ['lib/lean/Solidity/KeySort.olean']),
    'generator-solcases': (['solcases'], ['bin/solcases']),
    'clean-default': ([], ['lib/lean/Solidity.olean', 'bin/solkeycheck', 'bin/solidity-lean']),
    'clean-compiler': (['Solidity.Evm.Compiler'], ['lib/lean/Solidity/Evm/Compiler.olean']),
    'clean-frontend': (['Solidity.Frontend.Import'], ['lib/lean/Solidity/Frontend/Import.olean']),
}
TARGETS.update({'warm-' + k[6:]: v for k, v in list(TARGETS.items()) if k.startswith('clean-')})

TARGETS['warm-memory-calls']=(['Solidity.Evm.MemoryCallExamples'],['lib/lean/Solidity/Evm/MemoryCallExamples.olean'])
TARGETS['warm-memory-calls-observation']=([],['lib/lean/Solidity/Evm/MemoryCallExamples.olean'])


def memory_query_bytes():
    spec=importlib.util.spec_from_file_location('v17_memory_calls',ROOT/'scripts/roadmap-v17-memory-calls.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module.query_bytes()


def gate_command(gate,out):
    prefix=['lake','-f','roadmap-v17-runtime.lakefile.toml']
    if gate=='warm-memory-calls-observation':
        return prefix+['env','lean','-j1','--tstack=131072','--root='+str(out),str(out/'MemoryCallsQuery.lean')]
    return prefix+['build',*TARGETS[gate][0]]


def serial_config(root):
    return (root / 'lakefile.toml').read_bytes().replace(
        b'weakLeanArgs = ["--tstack=131072"]', b'weakLeanArgs = ["--tstack=131072", "-j1"]')


def inventory(path):
    e.require(not path.is_symlink(), 'symlink inventory root')
    path = path.resolve()
    files = {}
    if path.exists():
        for p in sorted(path.rglob('*')):
            e.require(not p.is_symlink(), 'symlink in build/cache inventory')
            if p.is_file():
                files[str(p.relative_to(path))] = resources.hash_file(p)
    return {'path': str(path), 'files': files}


def read_bound(root, name, sha):
    data = e.local_file(root, name).read_bytes()
    e.require(e.digest(data) == sha, 'corrupt provenance attachment: ' + name)
    return data


def validate(record, evidence_root, current, gate, gate_row=None):
    e.require(type(record['exit']) is int, 'invalid provenance exit')
    e.require(type(record['schema']) is int and record['schema']==3,'unsupported provenance schema')
    check_outcomes(record)
    e.require(Path(record['collectionDirectory']).resolve() == evidence_root.resolve(), 'wrong collection directory')
    e.require(type(record['schema']) is int and record['schema'] == 3 and record['gate'] == gate, 'wrong provenance gate')
    e.require(record['before'] == record['after'] == current, 'source/toolchain/input changed or mismatched')
    e.require(record['budgets'] == BUDGET, 'changed budget/threads')
    e.require(record['configurationSha256'] == record['configurationAfterSha256'] == current['serialConfigSha256'], 'changed configuration')
    read_bound(evidence_root, record['configuration'], record['configurationSha256'])
    read_bound(evidence_root, record['launcher'], record['launcherSha256'])
    e.require(record['launcherSha256'] == e.digest(launcher_bytes()), 'changed serial launcher')
    e.require(set(record['serializers']) == set(e.BUILD_TOOL_NAMES), 'missing serialized entrypoint')
    for tool, ref in record['serializers'].items():
        e.require(ref['path'] == tool + '-launcher', 'serializer is not the mounted source')
        raw = read_bound(evidence_root, ref['path'], ref['sha256'])
        e.require(raw == launcher_bytes(tool), 'changed tool serializer')
    e.require(record['launcher'] == record['serializers']['lean']['path'] and record['launcherSha256'] == record['serializers']['lean']['sha256'], 'Lean launcher pointer mismatch')
    e.require(runtime_tools(current) == record['buildTools'], 'changed serialized tool binaries')
    e.require(re.fullmatch(r'roadmap-v17-[0-9a-f]{32}', record['containerName']), 'wrong collection container identity')
    argv = e.loads(read_bound(evidence_root, record['dockerArgv'], record['dockerArgvSha256']))
    e.require(argv == docker_create_argv(evidence_root.resolve(), current, record['containerName'], record['command']), 'changed Docker spawn configuration')
    e.require(record['command'] == gate_command(gate,evidence_root.resolve()), 'wrong build command')
    if gate in ('warm-memory-calls','warm-memory-calls-observation'):
        e.require(record['installedBefore']==record['installedAfter']==resources.tool_inputs(current),'changed installed observation inputs')
    if gate=='warm-memory-calls-observation':
        e.require((evidence_root/'MemoryCallsQuery.lean').read_bytes()==memory_query_bytes(),'changed memory call query bytes')
    e.require(record['mode'] in ('clean', 'warm'), 'unknown cache mode')
    e.require(record['mode'] == ('clean' if gate.startswith('clean-') else 'warm'), 'warm result labeled clean')
    repository = Path(current['repository']).resolve()
    expected_build = repository / '.lake/build'
    expected_cache = repository / '.lake/roadmap-v17-cache' / current['sourceToolchainKey']
    e.require(expected_build.resolve() == expected_build and expected_cache.resolve() == expected_cache, 'symlinked build/cache root')
    for phase in ('Start', 'End'):
        build = record['build' + phase]
        cache = record['cache' + phase]
        e.require(build['path'] == str(expected_build), 'wrong build location')
        e.require(cache['path'] == str(expected_cache), 'wrong cache location')
        e.require(Path(cache['path']).name == current['sourceToolchainKey'], 'cache identity/source key mismatch')
        for inv in (build, cache):
            for path, sha in inv['files'].items():
                e.require(not Path(path).is_absolute() and '..' not in Path(path).parts and e.HEX.fullmatch(sha), 'invalid artifact inventory')
    if record['mode'] == 'clean':
        e.require(not record['buildStart']['files'] and not record['cacheStart']['files'], 'nonempty clean starting state')
    else:
        e.require(record['buildStart']['files'] or record['cacheStart']['files'], 'warm starting state is empty')
    runtime = e.loads(read_bound(evidence_root, record['runtime'], record['runtimeSha256']))
    e.require(runtime['entrypointHashes'] == {tool: e.digest(launcher_bytes(tool)) for tool in e.BUILD_TOOL_NAMES}, 'unwrapped runtime entrypoint')
    e.require(runtime['toolHashes'] == {k: v['sha256'] for k, v in current['buildTools'].items()}, 'observed build tool mismatch')
    e.require(all(type(runtime[k]) is int for k in ('memoryMax','swapMax','memoryPeak')),'invalid runtime memory measurements')
    e.require(runtime['memoryMax'] == CAP and runtime['swapMax'] == 0, 'missing/wrong cap or swap')
    e.require(runtime['realLeanSha256'] == current['runtime']['lean']['sha256'] and
              runtime['lakeSha256'] == current['runtime']['lake']['sha256'] and runtime['leanVersion'] == current['runtime']['lean']['version'] and runtime['lakeVersion'] == current['runtime']['lake']['version'] and runtime['leanNumThreads'] == '1', 'runtime binary mismatch')
    e.require(0 < runtime['memoryPeak'] <= CAP and runtime['image'] == IMAGE, 'invalid execution peak/image')
    e.require(record['sampleFormat'] == SAMPLE_FORMAT, 'unsupported process sample format')
    samples = e.loads(read_bound(evidence_root, record['samples'], record['samplesSha256']))
    e.require(samples and all(type(s['rssBytes']) is int and s['rssBytes'] >= 0 and type(s['leanWorkers']) is int and 0 <= s['leanWorkers'] <= 1 and type(s['leanSupervisors']) is int and s['leanSupervisors'] >= 0 and all(type(s.get(k)) is int and s[k] >= 0 for k in ('leanZombies', 'leanTransitions')) and type(s['unclassifiedLeanWorkers']) is int and s['unclassifiedLeanWorkers'] == 0 and s.get('unknownLeanProcesses') == [] for s in samples), 'missing/parallel execution samples')
    check_headroom(record)
    e.require(type(record['diskFreeBytes']) is int and record['diskFreeBytes'] >= 1024**3,'insufficient recorded disk')
    e.require(e.loads(read_bound(evidence_root,record['errors'],record['errorsSha256'])) == record['phaseErrors'],'changed phase errors')
    e.require(0 < record['elapsedSeconds'] <= BUDGET['processSeconds'] + 5, 'execution budget exceeded')
    execution = read_bound(evidence_root, record['executionScript'], record['executionScriptSha256'])
    e.require(execution == execution_script(evidence_root.resolve(), record['command'], Path(current['runtime']['lake']['path'])).encode(), 'changed execution script')
    log = read_bound(evidence_root, record['log'], record['logSha256'])
    e.require(log, 'missing execution output')
    if record['mode'] == 'clean': e.require(b'Fetched ' not in log, 'cache fetch labeled clean')
    if gate_row is not None:
        e.require(gate_row['exit'] == record['exit'] and gate_row['sha256'] == record['logSha256'] and
                  gate_row['log'] == record['log'] and gate_row['command'] == record['command'], 'gate/provenance disagreement')
    if record['exit'] == 0:
        e.require(all(p in record['buildEnd']['files'] for p in TARGETS[gate][1]), 'unmatched mandatory artifact')
        # Live files must match recorded outputs; no artifact/cache copies are exported.
        for kind in ('buildEnd', 'cacheEnd'):
            e.require(inventory(Path(record[kind]['path'])) == record[kind], 'live artifacts/cache differ')
    return record['exit'] == 0


def validate_pair(report, evidence_root, current):
    e.require(set(report['runs']) == {'clean', 'warm'}, 'missing mandatory clean/warm gate')
    runs = {}
    for mode, ref in report['runs'].items():
        run = e.loads(read_bound(evidence_root, ref['path'], ref['sha256']))
        e.require(run['mode'] == mode, 'wrong pair mode')
        directory = Path(run['collectionDirectory']).resolve()
        e.require(directory.is_relative_to(evidence_root.resolve()), 'pair collection escapes evidence root')
        e.require(validate(run, directory, current, run['gate']), 'nonzero mandatory gate')
        runs[mode] = run
    a, b = runs['clean'], runs['warm']
    e.require(a['gate'].replace('clean-', '') == b['gate'].replace('warm-', ''), 'unmatched targets')
    for kind in ('build', 'cache'):
        e.require(a[kind + 'End'] == b[kind + 'Start'], 'unmatched cache/build continuity')
        e.require(a[kind + 'End']['files'] == b[kind + 'End']['files'], 'unmatched clean/warm artifacts')
    return {'target': a['gate'][6:], 'accountingComplete': True, 'releaseClosed': False, 'boundary': 'Byte/provenance consistency only; independent kernel gates remain required.'}


def launcher_bytes(tool='lean'):
    e.require(tool in e.BUILD_TOOL_NAMES, 'unsupported serialized entrypoint')
    args = ' -j1' if tool == 'lean' else ''
    # FD 9 is inherited by the tool family. A stripped/forged family token fails
    # closed instead of recursively waiting on its own lock. The outer
    # shell supervisor also holds the descriptor until its direct child exits.
    return ("#!/bin/sh\n"
            "lock=/workspace/scratch/v17-build-process.lock\n"
            "if [ \"${V17_SERIAL_FAMILY-}\" = 1 ]; then\n"
            "  [ \"$(readlink /proc/self/fd/9)\" = \"$lock\" ] || exit 125\n"
            "  /usr/bin/flock -n -x 9 || exit 125\n"
            "  exec /opt/v17-toolchain/bin/" + tool + args + " \"$@\"\n"
            "fi\n"
            "exec 9>\"$lock\"\n"
            "export V17_SERIAL_FAMILY=1\n"
            "/usr/bin/flock -x 9 || exit 125\n"
            "/opt/v17-toolchain/bin/" + tool + args + " \"$@\"\n"
            "exit $?\n").encode()


def runtime_tools(current):
    return current['buildTools']


def docker(*args, **kwargs):
    env = os.environ.copy()
    for k in ('DOCKER_HOST', 'DOCKER_CONTEXT', 'DOCKER_TLS', 'DOCKER_TLS_VERIFY', 'DOCKER_CERT_PATH'): env.pop(k, None)
    kwargs.setdefault('timeout', 5)
    kwargs.setdefault('stdout', subprocess.PIPE)
    kwargs.setdefault('stderr', subprocess.PIPE)
    return subprocess.run(['docker', '--host=unix:///var/run/docker.sock', *args], env=env, check=True, **kwargs)


def execution_script(out, command, lake):
    script = 'set -eu\n'
    for name, source in [('memoryMax', '/sys/fs/cgroup/memory.max'), ('swapMax', '/sys/fs/cgroup/memory.swap.max')]:
        script += 'cat ' + source + ' > ' + shlex.quote(str(out / name)) + '\n'
    script += 'test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888\ntest "$(cat /sys/fs/cgroup/memory.swap.max)" = 0\n'
    for name, cmd in [('realLeanSha256', 'sha256sum /opt/v17-toolchain/bin/lean'), ('lakeSha256', 'sha256sum ' + shlex.quote(str(lake))), ('leanVersion', 'lean --version'), ('lakeVersion', 'lake --version'), ('leanNumThreads', 'printf %s "$LEAN_NUM_THREADS"')]:
        script += cmd + ' > ' + shlex.quote(str(out / name)) + '\n'
    for tool in e.BUILD_TOOL_NAMES:
        script += 'sha256sum /opt/v17-toolchain/bin/' + tool + ' > ' + shlex.quote(str(out / ('tool-' + tool))) + '\n'
        script += 'sha256sum ' + shlex.quote(str(lake.parent / tool)) + ' > ' + shlex.quote(str(out / ('entrypoint-' + tool))) + '\n'
    script += 'set +e\ntimeout --signal=KILL 300 ' + shlex.join(command) + '\nresult=$?\n'
    script += 'cat /sys/fs/cgroup/memory.peak > ' + shlex.quote(str(out / 'memoryPeak')) + '\nexit "$result"\n'
    return script


def docker_create_argv(out, current, container_name, command):
    repository = Path(current['repository'])
    lean = Path(current['runtime']['lean']['path'])
    lake = Path(current['runtime']['lake']['path'])
    cache = repository / '.lake/roadmap-v17-cache' / current['sourceToolchainKey']
    argv = ['create', '--name', container_name, '--network', 'none', '--memory', '12g', '--memory-swap', '12g', '--cpus', '1',
            '--mount', 'type=bind,src=/workspace,dst=/workspace',
            '--mount', f'type=bind,src={lean.parent.parent},dst=/opt/v17-toolchain,readonly']
    for tool in e.BUILD_TOOL_NAMES:
        argv += ['--mount', f'type=bind,src={out / (tool + "-launcher")},dst={lean.parent / tool},readonly']
    return argv + ['-w', str(repository), '-e', 'LEAN_NUM_THREADS=1', '-e', 'LEAN_SYSROOT=' + str(lean.parent.parent),
                   '-e', 'PATH=' + str(lean.parent) + ':/usr/local/bin:/usr/bin:/bin', '-e', 'LAKE_CACHE_DIR=' + str(cache),
                   IMAGE, 'sh', '-c', execution_script(out, command, lake)]


def process_sample(output, lean_path):
    """Observe native executables, supervisors, zombies and exec transitions.
    Unknown running commands remain fail-closed with their diagnostic context.
    Admission is enforced by the lock; ps sampling is not an atomic process proof.
    """
    lines = output.splitlines()
    e.require(lines and lines[0].split() == ['PID', 'STAT', 'COMMAND', 'RSS', 'COMMAND'], 'malformed process telemetry header')
    rss = native = supervisors = zombies = transitions = 0
    unknown = []
    for line in lines[1:]:
        if not line.strip(): continue
        fields = line.split(None, 4)
        e.require(len(fields) == 5 and fields[0].isdigit(), 'malformed process telemetry')
        amount = int(fields[3]); e.require(amount >= 0, 'negative process RSS')
        rss += amount * 1024
        args = fields[4].split()
        if fields[1].startswith('Z') and amount == 0 and fields[2] == 'lean': zombies += 1
        elif args[0] == '/opt/v17-toolchain/bin/lean': native += 1
        elif fields[2] == 'lean':
            if len(args) >= 2 and args[0] in ('/bin/sh', 'sh') and args[1] == str(lean_path): supervisors += 1
            elif args in (['/usr/bin/flock','-x','9'], ['/usr/bin/flock','-n','-x','9']): transitions += 1
            else: unknown.append({'pid':int(fields[0]),'state':fields[1],'rssBytes':amount*1024,'arguments':fields[4]})
    return {'rssBytes':rss,'leanWorkers':native,'leanSupervisors':supervisors,'leanZombies':zombies,
            'leanTransitions':transitions,'unclassifiedLeanWorkers':len(unknown),'unknownLeanProcesses':unknown}


def missing_container(error):
    return isinstance(error, subprocess.CalledProcessError) and error.returncode == 1 and any(
        text in str(error.stderr) for text in ('No such container', 'No such object'))


def ensure_no_unresolved():
    if not UNRESOLVED.exists(): return
    name = e.load(UNRESOLVED)['container']
    e.require(re.fullmatch(r'roadmap-v17-[0-9a-f]{32}', name), 'invalid unresolved container identity')
    try:
        state = docker('inspect','--format','{{.State.Status}}',name).stdout.decode().strip()
    except (OSError,subprocess.SubprocessError) as error:
        if missing_container(error): UNRESOLVED.unlink(); return
        raise ValueError('unresolved container; inspection failed: ' + str(error)) from error
    e.require(state in ('exited','dead'), 'unresolved task container may still run; refusing overlap')
    UNRESOLVED.unlink()


def final_exit(execution, cleanup, validation):
    return next((code for code in (execution,cleanup,validation) if code!=0),0)


def check_outcomes(r):
    raw=r['commandExit']
    e.require(raw is None or type(raw) is int and raw>=0,'invalid raw command exit')
    e.require(all(type(r[k]) is int and r[k]>=0 for k in ('executionExit','cleanupExit','validationExit')),'invalid phase exit')
    attach=r['attachExit']
    e.require(attach is None or type(attach) is int,'invalid attach exit')
    if r['executionExit']==0:
        e.require(raw==0 and attach==0,'raw/attach/execution exit disagreement')
    if raw is not None and raw!=0: e.require(r['executionExit']!=0,'nonzero command labeled pass')
    if attach is not None and attach!=0: e.require(r['executionExit']!=0,'nonzero transport labeled pass')
    e.require(r['exit']==final_exit(r['executionExit'],r['cleanupExit'],r['validationExit']),'overall/phase exit disagreement')
    e.require(isinstance(r['phaseErrors'],list) and all(isinstance(x,dict) and isinstance(x.get('phase'),str) and isinstance(x.get('error'),str) for x in r['phaseErrors']),'missing/malformed phase errors')
    e.require(r['exit']!=0 or not r['phaseErrors'],'errors contradict successful collection')


def collect(args):
    ensure_no_unresolved()
    out = args.out.resolve()
    e.require(not out.is_relative_to(ROOT), 'evidence must be outside checkout')
    out.mkdir(parents=True, exist_ok=False)
    before = e.snapshot(ROOT)
    cache = ROOT / '.lake/roadmap-v17-cache' / before['sourceToolchainKey']
    build = ROOT / '.lake/build'
    cache.mkdir(parents=True, exist_ok=True)
    start_build, start_cache = inventory(build), inventory(cache)
    mode = 'clean' if args.gate.startswith('clean-') else 'warm'
    if mode == 'clean': e.require(not start_build['files'] and not start_cache['files'], 'refusing nonempty clean start; no cache/build deletion performed')
    installed_before = resources.tool_inputs(before) if args.gate in ('warm-memory-calls','warm-memory-calls-observation') else None
    resource_fields = resource_snapshot(); check_headroom(resource_fields)
    disk = os.statvfs(ROOT); free = disk.f_bavail * disk.f_frsize
    e.require(free >= 1024**3, 'disk guard')
    cfg = serial_config(ROOT); (out / 'configuration.toml').write_bytes(cfg)
    serializers = {}
    for tool in e.BUILD_TOOL_NAMES:
        name = tool + '-launcher'
        data = launcher_bytes(tool)
        (out / name).write_bytes(data); (out / name).chmod(0o755)
        serializers[tool] = {'path': name, 'sha256': e.digest(data)}
    config = ROOT / 'roadmap-v17-runtime.lakefile.toml'
    e.require(not config.exists(), 'runtime config collision')
    lean = Path(__import__('shutil').which('lean')).resolve(); lake = Path(__import__('shutil').which('lake')).resolve()
    e.require(lean.parent == lake.parent, 'non-collocated Lean/Lake toolchain')
    command = gate_command(args.gate,out)
    if args.gate=='warm-memory-calls-observation': (out/'MemoryCallsQuery.lean').write_bytes(memory_query_bytes())
    script = execution_script(out, command, lake)
    (out/'execution.sh').write_text(script)
    container_name = 'roadmap-v17-' + uuid.uuid4().hex
    UNRESOLVED.write_text(json.dumps({'container':container_name,'revision':before['revision']}))
    cid = None; proc = None; samples = []; errors = []; begin = time.monotonic(); code = 125; command_exit = None; attach_exit = None; cleanup_exit = 0; validation_exit = 0
    def remaining():
        left = BUDGET['processSeconds'] - (time.monotonic() - begin)
        if left <= 0: raise subprocess.TimeoutExpired('V17 build deadline', 300)
        return min(5, left)
    try:
        config.write_bytes(cfg)
        create = docker_create_argv(out, before, container_name, command)
        (out/'docker-argv.json').write_text(json.dumps(create))
        cid = docker(*create, timeout=remaining()).stdout.decode().strip()
        with (out / 'build.log').open('wb') as log:
            env = os.environ.copy()
            for k in ('DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH'): env.pop(k,None)
            proc = subprocess.Popen(['docker','--host=unix:///var/run/docker.sock','start','-a',cid], env=env, stdout=log, stderr=subprocess.STDOUT)
            while True:
                state = docker('inspect','--format','{{.State.Status}}',cid,timeout=remaining()).stdout.decode().strip()
                if state in ('exited','dead'):
                    raw_exit=docker('inspect','--format','{{.State.ExitCode}}',cid,timeout=remaining()).stdout.decode().strip()
                    e.require(re.fullmatch(r'0|[1-9][0-9]*',raw_exit),'invalid container command exit')
                    command_exit=int(raw_exit)
                    attach_exit=proc.wait(timeout=remaining())
                    code=command_exit if command_exit else (attach_exit if attach_exit is not None and attach_exit>=0 else 125)
                    break
                if state == 'running':
                    try:
                        top = docker('top',cid,'-ww','-eo','pid,stat,comm,rss,args',timeout=remaining()).stdout.decode()
                    except subprocess.CalledProcessError:
                        # Re-inspect a possible rapid exit, retaining the error if still running.
                        if docker('inspect','--format','{{.State.Status}}',cid,timeout=remaining()).stdout.decode().strip() == 'running': raise
                        continue
                    samples.append(process_sample(top, lean))
                elif state != 'created':
                    raise ValueError('unexpected container state: ' + state)
                remaining(); time.sleep(0.05)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        errors.append({'phase':'execution','error':str(error), 'stderr':str(getattr(error,'stderr',None))})
        code = 124 if isinstance(error,subprocess.TimeoutExpired) else 125
    finally:
        execution_elapsed = time.monotonic() - begin
        execution_exit = code
        try:
            docker('rm','-f',container_name,timeout=5)
            UNRESOLVED.unlink(missing_ok=True)
        except (OSError,subprocess.SubprocessError) as error:
            if missing_container(error): UNRESOLVED.unlink(missing_ok=True)
            else:
                errors.append({'phase':'container cleanup','error':str(error),'stderr':str(getattr(error,'stderr',None))}); cleanup_exit = 125
        finally:
            if proc and proc.poll() is None:
                proc.kill()
                try: proc.wait(timeout=2)
                except subprocess.TimeoutExpired: errors.append({'phase':'attach cleanup','error':'client did not reap'}); cleanup_exit=125
            config_after = None
            try:
                config_after = e.digest(config.read_bytes()) if config.exists() else None
                config.unlink(missing_ok=True)
            except OSError as error:
                errors.append({'phase':'configuration cleanup','error':str(error)}); cleanup_exit=125
    try: after = e.snapshot(ROOT)
    except (OSError,ValueError,subprocess.SubprocessError) as error:
        after = {'error':str(error)}; errors.append({'phase':'after snapshot','error':str(error)}); validation_exit = 125
    def observed(name, default=''):
        path=out/name
        try: return path.read_text().strip() if path.exists() else default
        except OSError as error:
            errors.append({'phase':'runtime observation','error':str(error)}); return default
    def observed_int(name,default):
        raw=observed(name,str(default))
        if not re.fullmatch(r'-?[0-9]+',raw):
            errors.append({'phase':'runtime observation','error':'malformed '+name}); return default
        return int(raw)
    runtime = {'entrypointHashes': {tool: observed('entrypoint-' + tool).split(' ')[0] for tool in e.BUILD_TOOL_NAMES}, 'toolHashes': {tool: observed('tool-' + tool).split(' ')[0] for tool in e.BUILD_TOOL_NAMES}, 'memoryMax':observed_int('memoryMax',-1), 'swapMax':observed_int('swapMax',-1),
               'memoryPeak':observed_int('memoryPeak',0),
               'realLeanSha256':observed('realLeanSha256').split(' ')[0], 'lakeSha256':observed('lakeSha256').split(' ')[0],
               'image':IMAGE,'leanVersion':observed('leanVersion'),'lakeVersion':observed('lakeVersion'),'leanNumThreads':observed('leanNumThreads')}
    if any(x['phase']=='runtime observation' for x in errors): validation_exit=125
    (out/'execution-errors.json').write_text(json.dumps(errors,indent=2))
    (out/'runtime.json').write_text(json.dumps(runtime))
    (out/'samples.json').write_text(json.dumps(samples))
    if not (out/'build.log').exists(): (out/'build.log').write_text('Execution failed before build start.\n')
    record = {'schema':3,'sampleFormat':SAMPLE_FORMAT,'containerName':container_name,'dockerArgv':'docker-argv.json','dockerArgvSha256':e.digest((out/'docker-argv.json').read_bytes()) if (out/'docker-argv.json').exists() else None,'serializers':serializers,'buildTools':runtime_tools(before),'collectionDirectory':str(out),'gate':args.gate,'mode':mode,'command':command,'before':before,'after':after,
              'budgets':BUDGET,'configuration':'configuration.toml','configurationSha256':e.digest(cfg),'configurationAfterSha256':config_after,
              'launcher':'lean-launcher','launcherSha256':e.digest(launcher_bytes()),
              'runtime':'runtime.json','runtimeSha256':e.digest((out/'runtime.json').read_bytes()),
              'samples':'samples.json','samplesSha256':e.digest((out/'samples.json').read_bytes()),
              'log':'build.log','logSha256':e.digest((out/'build.log').read_bytes()),'commandExit':command_exit,'attachExit':attach_exit,'executionExit':execution_exit,'cleanupExit':cleanup_exit,'validationExit':validation_exit,'phaseErrors':errors,'errors':'execution-errors.json','errorsSha256':e.digest((out/'execution-errors.json').read_bytes()),'exit':final_exit(execution_exit,cleanup_exit,validation_exit),
              **resource_fields,'diskFreeBytes':free,'elapsedSeconds':execution_elapsed,
              'executionScript':'execution.sh','executionScriptSha256':e.digest((out/'execution.sh').read_bytes()),
              'buildStart':start_build,'cacheStart':start_cache,'buildEnd':inventory(build),'cacheEnd':inventory(cache),
              'releaseClosed':False}
    if installed_before is not None:
        record['installedBefore']=installed_before
        try: record['installedAfter']=resources.tool_inputs(before)
        except (OSError,ValueError) as error:
            record['installedAfter']=None; record['validationExit']=125; record['exit']=final_exit(execution_exit,cleanup_exit,125); errors.append({'phase':'installed inputs after','error':str(error)})
            (out/'execution-errors.json').write_text(json.dumps(errors,indent=2));record['errorsSha256']=e.digest((out/'execution-errors.json').read_bytes())
    if record['exit']==0:
        try: validate(record,out,before,args.gate)
        except (ValueError,KeyError,TypeError,OSError,subprocess.SubprocessError) as error:
            record['validationExit']=125; errors.append({'phase':'validation','error':str(error)})
            record['exit']=final_exit(execution_exit,cleanup_exit,125)
            (out/'execution-errors.json').write_text(json.dumps(errors,indent=2))
            record['errorsSha256']=e.digest((out/'execution-errors.json').read_bytes())
    (out/'provenance.json').write_text(json.dumps(record,indent=2)+'\n')
    return record['exit']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=['collect','validate','pair'])
    p.add_argument('--gate', choices=TARGETS)
    p.add_argument('--out', type=Path)
    p.add_argument('--report', type=Path)
    p.add_argument('--evidence-root', type=Path)
    a=p.parse_args()
    if a.mode=='collect':
        e.require(a.gate and a.out, '--gate/--out required')
        with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a+') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            return collect(a)
    current=e.snapshot(ROOT)
    e.require(a.report and a.evidence_root, '--report/--evidence-root required')
    r=e.load(a.report)
    result=validate_pair(r,a.evidence_root,current) if a.mode=='pair' else {'accountingComplete':validate(r,a.evidence_root,current,r['gate']),'releaseClosed':False}
    print(json.dumps(result)); return 0 if result['accountingComplete'] else 1


if __name__=='__main__':
    try: raise SystemExit(main())
    except (ValueError,KeyError,TypeError,OSError,subprocess.SubprocessError) as err:
        print(json.dumps({'error':str(err),'releaseClosed':False})); raise SystemExit(2)
