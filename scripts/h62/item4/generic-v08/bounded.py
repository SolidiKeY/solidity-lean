#!/usr/bin/env python3
"""One bounded process group; report actual resource/time data, never a fake pass."""
import argparse,json,os,pathlib,resource,signal,subprocess,time
p=argparse.ArgumentParser(__doc__)
p.add_argument('--record',type=pathlib.Path,required=True)
p.add_argument('--seconds',type=int,default=300)
p.add_argument('command',nargs=argparse.REMAINDER)
a=p.parse_args()
cmd=a.command[1:] if a.command[:1]==['--'] else a.command
if not cmd: p.error('command required')
if pathlib.Path(cmd[0]).name != 'lean' or '-j1' not in cmd:
    p.error('only a direct Lean command with explicit -j1 is supported')

def preexec():
    os.setsid()
    resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))

def available():
    fields=dict(line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines())
    host=int(fields['MemAvailable'].split()[0])*1024
    cap=pathlib.Path('/sys/fs/cgroup/memory.max').read_text().strip()
    current=int(pathlib.Path('/sys/fs/cgroup/memory.current').read_text())
    return min(host,int(cap)-current) if cap!='max' else host

if available()<4*1024**3: raise SystemExit('BLOCKED: less than 4 GiB headroom')
if int(pathlib.Path('/proc/meminfo').read_text().split('SwapTotal:')[1].split()[0])!=0:
    raise SystemExit('BLOCKED: active swap configuration requires no-swap isolation')
start=time.monotonic()
env=dict(os.environ,LEAN_NUM_THREADS='1')
proc=subprocess.Popen(cmd,env=env,preexec_fn=preexec)
stop=None
while proc.poll() is None:
    if time.monotonic()-start>a.seconds: stop='timeout'
    elif available()<4*1024**3: stop='headroom'
    if stop:
        os.killpg(proc.pid,signal.SIGTERM)
        try: proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid,signal.SIGKILL); proc.wait()
        break
    time.sleep(.25)
# A successful parent must not leave its process group alive.
try:
    os.killpg(proc.pid,0)
except ProcessLookupError:
    pass
else:
    os.killpg(proc.pid,signal.SIGKILL)
    stop=stop or 'surviving-process-group'
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
record=dict(command=cmd,exit=proc.returncode,stop=stop,wall_seconds=time.monotonic()-start,
            cpu_seconds=usage.ru_utime+usage.ru_stime,max_rss_kib=usage.ru_maxrss,
            requested_threads=1,per_process_address_space_bytes=12*1024**3,headroom_bytes=4*1024**3,
            rss_measurement='RUSAGE_CHILDREN high-water; not aggregate RSS')
a.record.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
raise SystemExit(1 if stop else proc.returncode)
