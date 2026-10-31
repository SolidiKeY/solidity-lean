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
UNRESOLVED = Path('/workspace/scratch/v17-unresolved-container.json')
CAP = 12 * 1024**3
BUDGET = {'processSeconds': 300, 'suiteModuleSeconds': 300, 'leanNumThreads': 1}
SAMPLE_FORMAT = 'pid-comm-rss-args/native-v1'
IMAGE = 'debian@sha256:99c0b25c46d0214d5a2091092e7908907dcaecd6a962cde0ac700acee222b6f3'
TARGETS = {
    'runtime-keysort': (['Solidity.KeySort'], ['lib/lean/Solidity/KeySort.olean']),
    'generator-solcases': (['solcases'], ['bin/solcases']),
    'clean-default': ([], ['lib/lean/Solidity.olean', 'bin/solkeycheck', 'bin/solidity-lean']),
    'clean-compiler': (['Solidity.Evm.Compiler'], ['lib/lean/Solidity/Evm/Compiler.olean']),
    'clean-frontend': (['Solidity.Frontend.Import'], ['lib/lean/Solidity/Frontend/Import.olean']),
}
TARGETS.update({'warm-' + k[6:]: v for k, v in list(TARGETS.items()) if k.startswith('clean-')})


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
                with p.open('rb') as stream: files[str(p.relative_to(path))] = hashlib.file_digest(stream, 'sha256').hexdigest()
    return {'path': str(path), 'files': files}


def read_bound(root, name, sha):
    data = e.local_file(root, name).read_bytes()
    e.require(e.digest(data) == sha, 'corrupt provenance attachment: ' + name)
    return data


def validate(record, evidence_root, current, gate, gate_row=None):
    e.require(type(record['exit']) is int, 'invalid provenance exit')
    e.require(Path(record['collectionDirectory']).resolve() == evidence_root.resolve(), 'wrong collection directory')
    e.require(record['schema'] == 2 and record['gate'] == gate, 'wrong provenance gate')
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
    e.require(record['command'] == ['lake', '-f', 'roadmap-v17-runtime.lakefile.toml', 'build', *TARGETS[gate][0]], 'wrong build command')
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
    e.require(runtime['memoryMax'] == CAP and runtime['swapMax'] == 0, 'missing/wrong cap or swap')
    e.require(runtime['realLeanSha256'] == current['runtime']['lean']['sha256'] and
              runtime['lakeSha256'] == current['runtime']['lake']['sha256'] and runtime['leanVersion'] == current['runtime']['lean']['version'] and runtime['lakeVersion'] == current['runtime']['lake']['version'] and runtime['leanNumThreads'] == '1', 'runtime binary mismatch')
    e.require(0 < runtime['memoryPeak'] <= CAP and runtime['image'] == IMAGE, 'invalid execution peak/image')
    e.require(record['sampleFormat'] == SAMPLE_FORMAT, 'unsupported process sample format')
    samples = e.loads(read_bound(evidence_root, record['samples'], record['samplesSha256']))
    e.require(samples and all(type(s['rssBytes']) is int and s['rssBytes'] >= 0 and type(s['leanWorkers']) is int and 0 <= s['leanWorkers'] <= 1 and type(s['leanSupervisors']) is int and s['leanSupervisors'] >= 0 and type(s['unclassifiedLeanWorkers']) is int and s['unclassifiedLeanWorkers'] == 0 for s in samples), 'missing/parallel execution samples')
    e.require(record['headroomBytes'] >= 2 * 1024**3 and record['diskFreeBytes'] >= 1024**3, 'insufficient recorded headroom/disk')
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
    """Count actual native Lean executables, retaining supervisor/unknown counts.
    Admission is enforced by the lock; a sample is not an absence-of-overlap proof.
    """
    lines = output.splitlines()
    e.require(lines and lines[0].split() == ['PID', 'COMMAND', 'RSS', 'COMMAND'], 'malformed process telemetry header')
    rss = native = supervisors = unknown = 0
    for line in lines[1:]:
        if not line.strip(): continue
        fields = line.split(None, 3)
        e.require(len(fields) == 4 and fields[0].isdigit(), 'malformed process telemetry')
        amount = int(fields[2]); e.require(amount >= 0, 'negative process RSS')
        rss += amount * 1024
        if fields[1] != 'lean': continue
        args = fields[3].split()
        if args[0] == '/opt/v17-toolchain/bin/lean': native += 1
        elif len(args) >= 2 and args[0] in ('/bin/sh', 'sh') and args[1] == str(lean_path): supervisors += 1
        else: unknown += 1
    return {'rssBytes':rss, 'leanWorkers':native, 'leanSupervisors':supervisors, 'unclassifiedLeanWorkers':unknown}


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
    headroom = int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:'))) * 1024
    disk = os.statvfs(ROOT); free = disk.f_bavail * disk.f_frsize
    e.require(headroom >= 2 * 1024**3 and free >= 1024**3, 'headroom/disk guard')
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
    command = ['lake', '-f', config.name, 'build', *TARGETS[args.gate][0]]
    script = execution_script(out, command, lake)
    (out/'execution.sh').write_text(script)
    container_name = 'roadmap-v17-' + uuid.uuid4().hex
    UNRESOLVED.write_text(json.dumps({'container':container_name,'revision':before['revision']}))
    cid = None; proc = None; samples = []; errors = []; begin = time.monotonic(); code = 125
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
                    code = proc.wait(timeout=remaining()); break
                if state == 'running':
                    try:
                        top = docker('top',cid,'-ww','-eo','pid,comm,rss,args',timeout=remaining()).stdout.decode()
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
        try:
            docker('rm','-f',container_name,timeout=5)
            UNRESOLVED.unlink(missing_ok=True)
        except (OSError,subprocess.SubprocessError) as error:
            if missing_container(error): UNRESOLVED.unlink(missing_ok=True)
            else:
                errors.append({'phase':'container cleanup','error':str(error),'stderr':str(getattr(error,'stderr',None))}); code = 125
        finally:
            if proc and proc.poll() is None:
                proc.kill()
                try: proc.wait(timeout=2)
                except subprocess.TimeoutExpired: errors.append({'phase':'attach cleanup','error':'client did not reap'})
            config_after = e.digest(config.read_bytes()) if config.exists() else None
            config.unlink(missing_ok=True)
    try: after = e.snapshot(ROOT)
    except (OSError,ValueError,subprocess.SubprocessError) as error:
        after = {'error':str(error)}; errors.append({'phase':'after snapshot','error':str(error)}); code = 125
    (out/'execution-errors.json').write_text(json.dumps(errors,indent=2))
    def observed(name, default=''):
        path=out/name
        return path.read_text().strip() if path.exists() else default
    runtime = {'entrypointHashes': {tool: observed('entrypoint-' + tool).split(' ')[0] for tool in e.BUILD_TOOL_NAMES}, 'toolHashes': {tool: observed('tool-' + tool).split(' ')[0] for tool in e.BUILD_TOOL_NAMES}, 'memoryMax':int(observed('memoryMax','-1')), 'swapMax':int(observed('swapMax','-1')),
               'memoryPeak':int(observed('memoryPeak','0')),
               'realLeanSha256':observed('realLeanSha256').split(' ')[0], 'lakeSha256':observed('lakeSha256').split(' ')[0],
               'image':IMAGE,'leanVersion':observed('leanVersion'),'lakeVersion':observed('lakeVersion'),'leanNumThreads':observed('leanNumThreads')}
    (out/'runtime.json').write_text(json.dumps(runtime))
    (out/'samples.json').write_text(json.dumps(samples))
    if not (out/'build.log').exists(): (out/'build.log').write_text('Execution failed before build start.\n')
    record = {'schema':2,'sampleFormat':SAMPLE_FORMAT,'containerName':container_name,'dockerArgv':'docker-argv.json','dockerArgvSha256':e.digest((out/'docker-argv.json').read_bytes()) if (out/'docker-argv.json').exists() else None,'serializers':serializers,'buildTools':runtime_tools(before),'collectionDirectory':str(out),'gate':args.gate,'mode':mode,'command':command,'before':before,'after':after,
              'budgets':BUDGET,'configuration':'configuration.toml','configurationSha256':e.digest(cfg),'configurationAfterSha256':config_after,
              'launcher':'lean-launcher','launcherSha256':e.digest(launcher_bytes()),
              'runtime':'runtime.json','runtimeSha256':e.digest((out/'runtime.json').read_bytes()),
              'samples':'samples.json','samplesSha256':e.digest((out/'samples.json').read_bytes()),
              'log':'build.log','logSha256':e.digest((out/'build.log').read_bytes()),'exit':code,
              'headroomBytes':headroom,'diskFreeBytes':free,'elapsedSeconds':execution_elapsed,
              'executionScript':'execution.sh','executionScriptSha256':e.digest((out/'execution.sh').read_bytes()),
              'buildStart':start_build,'cacheStart':start_cache,'buildEnd':inventory(build),'cacheEnd':inventory(cache),
              'releaseClosed':False}
    (out/'provenance.json').write_text(json.dumps(record,indent=2)+'\n')
    return code


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
