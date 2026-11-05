#!/usr/bin/env python3
"""Run the unchanged fresh 24-module gate; every Lean child stays in the task cap.
No existing runner/sidecar is modified. One shared 300-second deadline applies
both to the host orchestrator and each in-container Lean invocation.
"""
import fcntl, hashlib, json, os, pathlib, signal, subprocess, sys, time
ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = pathlib.Path('/workspace/v07-evidence/restart-20261102/effects-fresh-replay')
RUNTIME = 'v07-h2-reusable'
DOCKER = ['docker', '--host=unix:///var/run/docker.sock']
ENV = os.environ.copy()
for key in ['DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH']:
    ENV.pop(key, None)
lock = open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
os.chdir(ROOT)
assert int(next(x.split()[1] for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))) >= 4194304
OUT.mkdir(exist_ok=False)
def docker(args, **kwargs):
    return subprocess.run(DOCKER + args, env=ENV, check=True, timeout=10, **kwargs)
container = json.loads(docker(['inspect',RUNTIME],capture_output=True,text=True).stdout)[0]
(OUT/'container.json').write_text(json.dumps(container,indent=2)+'\n')
assert container['Config']['WorkingDir']==str(ROOT)
h = container['HostConfig']
assert container['State']['Running'] and h['Memory']==12884901888 and h['MemorySwap']==12884901888
assert h['NanoCpus']==1000000000 and h['NetworkMode']=='none'
assert container['Image']=='sha256:354cdc53abb843ea02e9a72c153b000c290014d8a90aba62897c143710a5667f'
mounts={m['Destination']:m for m in container['Mounts']}
assert mounts[str(ROOT)]['Source']==str(ROOT) and mounts[str(ROOT)]['RW']
assert mounts['/toolchain']['Source']=='/workspace/.setup/tools/lean-4.24.0-linux' and not mounts['/toolchain']['RW']
assert mounts['/evidence']['Source']=='/workspace/v07-evidence' and mounts['/evidence']['RW']
assert int(pathlib.Path('/sys/fs/cgroup/memory.max').read_text())==17179869184
parent_swap_max=pathlib.Path('/sys/fs/cgroup/memory.swap.max').read_text().strip()
assert int(next(x.split()[1] for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('SwapTotal:')))==0
assert len(pathlib.Path('/proc/swaps').read_text().splitlines())==1
(OUT/'parent-resources.json').write_text(json.dumps(dict(memoryMax=17179869184,swapMax=parent_swap_max,hostSwapTotalKiB=0,cgroup=pathlib.Path('/proc/self/cgroup').read_text()))+'\n')
resources = ['exec',RUNTIME,'sh','-c','test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888 && test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0 && cat /sys/fs/cgroup/memory.events /sys/fs/cgroup/memory.peak /sys/fs/cgroup/memory.swap.current']
(OUT/'resources-before.txt').write_text(docker(resources,capture_output=True,text=True).stdout)
shimdir=OUT/'bin';shimdir.mkdir()
shim=shimdir/'lean'
entry='remaining=$(awk -v deadline="$1" \'BEGIN{getline < "/proc/uptime"; remaining=deadline-$1; if(remaining<=0) exit 1; printf "%.6f",remaining}\') || exit 124; shift; exec timeout -s KILL "${remaining}s" lean "$@"'
shim_body="#!/usr/bin/env python3\nimport json,os,subprocess,sys,time\nremaining=float(os.environ['V07_REPLAY_DEADLINE'])-time.monotonic()\nif remaining<=0:raise SystemExit(124)\nshell=__ENTRY__\ncommand=['docker','--host=unix:///var/run/docker.sock','exec','-e','LEAN_NUM_THREADS=1','v07-h2-reusable','sh','-c',shell,'replay',os.environ['V07_REPLAY_UPTIME_DEADLINE']]+sys.argv[1:]\nwith open(os.environ['V07_REPLAY_COMMANDS'],'a') as f:f.write(json.dumps(dict(command=command,remainingSeconds=remaining))+'\\n')\nraise SystemExit(subprocess.run(command).returncode)\n"
shim.write_text(shim_body.replace("__ENTRY__",repr(entry)))
shim.chmod(0o755)
top_args=['top',RUNTIME,'-eo','pid,stat,comm,args']
def active_workers(top):
    return [line for line in top.splitlines()[1:] if len(line.split())>=3 and not line.split()[1].startswith('Z') and line.split()[2] in ['lean','lake','clang','leanc','ld.lld']]
assert not active_workers(docker(top_args,capture_output=True,text=True).stdout), 'competing worker before workload'
clock_before=time.monotonic()
container_uptime=float(docker(['exec',RUNTIME,'cat','/proc/uptime'],capture_output=True,text=True).stdout.split()[0])
clock_after=time.monotonic()
uptime_offset=container_uptime-clock_after
(OUT/'clocks.json').write_text(json.dumps(dict(hostBefore=clock_before,hostAfter=clock_after,containerUptime=container_uptime,conservativeOffset=uptime_offset),indent=2)+'\n')
monitor_path='/evidence/restart-20261102/effects-fresh-replay/monitor.pid'
with (OUT/'rss.tsv').open('wb') as rss:
    monitor=subprocess.Popen(DOCKER+['exec',RUNTIME,'sh','-c','echo $$ > '+monitor_path+'; exec sh tests/v07/sample-memory.sh'],env=ENV,stdout=rss,stderr=subprocess.STDOUT)
    code=None;timedout=False;interrupted=False;worker=None;errors=[];start=time.monotonic()
    def retain_error(stage,error):
        errors.append(dict(stage=stage,error=repr(error),seconds=time.monotonic()-start))
        try:(OUT/'cleanup-errors.json').write_text(json.dumps(errors,indent=2)+'\n')
        except BaseException as logging_error:
            try:print('cleanup log failure',repr(logging_error),repr(error),file=sys.stderr,flush=True)
            except BaseException:pass
    try:
        env=ENV.copy();env['PATH']=str(shimdir)+os.pathsep+env['PATH'];env['LEAN_NUM_THREADS']='1'
        env['V07_REPLAY_DEADLINE']=str(start+300);env['V07_REPLAY_UPTIME_DEADLINE']=str(start+300+uptime_offset);env['V07_REPLAY_COMMANDS']=str(OUT/'commands.jsonl')
        output=ROOT/'.lake/v07-effects-fresh-replay'
        assert not output.exists()
        command=[sys.executable,'scripts/check-memory-loop-timing.py','--output',str(output),'--results',str(OUT/'results.json')]
        (OUT/'invocation.json').write_text(json.dumps(dict(command=command,budgetSeconds=300,runnerSha256=hashlib.sha256((ROOT/command[1]).read_bytes()).hexdigest()),indent=2)+'\n')
        with (OUT/'runner.log').open('wb') as log:
            worker=subprocess.Popen(command,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            try:code=worker.wait(timeout=max(0.001,start+300-time.monotonic()))
            except subprocess.TimeoutExpired:
                timedout=True;interrupted=True;os.killpg(worker.pid,signal.SIGKILL);worker.wait();code=124
    except BaseException as error:
        interrupted=True;retain_error('workload exception',error);code=1
    finally:
        work_seconds=time.monotonic()-start
        # Resolve all host exceptions before inspecting the owned runtime.
        # Even Docker inspection failures retain this controller and writer lock.
        if worker is not None:
            while True:
                try:
                    try:os.killpg(worker.pid,signal.SIGKILL)
                    except ProcessLookupError:pass
                    worker.wait(timeout=1)
                    active_host=[]
                    for status in pathlib.Path('/proc').glob('[0-9]*/stat'):
                        try:
                            fields=status.read_text().rsplit(')',1)[1].split()
                            if int(fields[2])==worker.pid and fields[0]!='Z':active_host.append(str(status))
                        except FileNotFoundError:pass
                    if not active_host:break
                    retain_error('waiting for owned host group',active_host)
                except BaseException as error:retain_error('host worker cleanup',error)
                time.sleep(1)
        # A canceled Docker request could still be queued. The shim checks the
        # absolute deadline inside the container; wait it out after interruption
        # so no queued request can later begin a Lean check after lock release.
        if interrupted:
            while time.monotonic()<start+300:
                try:time.sleep(min(1,start+300-time.monotonic()))
                except BaseException as error:retain_error('interrupted cleanup wait',error)
        while True:
            try:
                top=docker(top_args,capture_output=True,text=True).stdout
                (OUT/'processes-after.txt').write_text(top)
                active=active_workers(top)
                if not active:break
                retain_error('waiting for container deadline',active)
            except BaseException as error:retain_error('process inspection',error)
            time.sleep(1)
        # Monitor cleanup is independent of workload success/failure. Do not
        # mask the original gate exit with a monitor or metadata failure.
        while True:
            try:
                pid_file=OUT/'monitor.pid'
                if not pid_file.exists():
                    if monitor.poll() is not None:break
                    time.sleep(1);continue
                pid=int(pid_file.read_text());assert pid>1
                command='if test -r /proc/$1/cmdline; then case "$(tr "\\000" " " </proc/$1/cmdline)" in *"sh tests/v07/sample-memory.sh"*) kill -TERM "$1";; *) exit 79;; esac; fi'
                docker(['exec',RUNTIME,'sh','-c',command,'monitor',str(pid)])
                break
            except BaseException as error:retain_error('monitor stop',error);time.sleep(1)
        while True:
            try:monitor_code=monitor.wait(timeout=10);break
            except BaseException as error:retain_error('monitor wait',error)
        while True:
            try:
                (OUT/'resources-after.txt').write_text(docker(resources,capture_output=True,text=True).stdout)
                break
            except BaseException as error:retain_error('final resource snapshot',error);time.sleep(1)
        final_code=code if code else (monitor_code or (1 if errors else 0))
        (OUT/'controller.json').write_text(json.dumps(dict(exit_code=final_code,gate_exit=code,timedout=timedout,budgetSeconds=300,workSeconds=work_seconds,cleanupSeconds=time.monotonic()-start-work_seconds,monitor_exit=monitor_code,cleanup_errors=errors),indent=2)+'\n')
        code=final_code
print('fresh replay exit',code,'timeout',timedout,flush=True)
raise SystemExit(code)
