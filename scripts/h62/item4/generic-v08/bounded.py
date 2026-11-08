#!/usr/bin/env python3
"""One bounded process group; report actual resource/time data, never a fake pass."""
import argparse,json,os,pathlib,resource,signal,subprocess,time
from width_resources import process_usage
p=argparse.ArgumentParser(__doc__)
p.add_argument('--record',type=pathlib.Path,required=True)
p.add_argument('--seconds',type=int,default=300)
p.add_argument('--aggregate',action='store_true',help='Also enforce aggregate12GiB RSS and one Lean process')
p.add_argument('--aggregate-parent',action='store_true',help='Include the serial v2 driver RSS')
p.add_argument('--parent-pid',type=int,help='Original v2 driver; never follow reparenting')
p.add_argument('command',nargs=argparse.REMAINDER)
a=p.parse_args()
cmd=a.command[1:] if a.command[:1]==['--'] else a.command
if not cmd: p.error('command required')
if a.aggregate_parent and not a.aggregate: p.error('--aggregate-parent requires --aggregate')
if a.aggregate_parent and (a.parent_pid is None or a.parent_pid <= 1):
    p.error('--aggregate-parent requires the original --parent-pid')
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
original_parent=a.parent_pid if a.aggregate_parent else None
if original_parent is not None and os.getppid()!=original_parent:
    raise SystemExit('BLOCKED: original driver was lost before spawn')
start=time.monotonic()
env=dict(os.environ,LEAN_NUM_THREADS='1')
proc=None
stop=None
monitor_error=None
peak_aggregate=0
max_lean_processes=0
handlers={}
if a.aggregate:
    def interrupted(signum, _frame):
        raise RuntimeError('monitor interrupted by signal ' + str(signum))
    for signum in (signal.SIGTERM, signal.SIGINT):
        handlers[signum]=signal.signal(signum, interrupted)
try:
    proc=subprocess.Popen(cmd,env=env,preexec_fn=preexec)
    while proc.poll() is None:
        if original_parent is not None and os.getppid()!=original_parent:
            stop='parent-lost'
            break
        if time.monotonic()-start>a.seconds: stop='timeout'
        elif available()<4*1024**3: stop='headroom'
        if a.aggregate:
            rss, lean_processes = process_usage(proc.pid)
            for pid in [os.getpid()] + ([original_parent] if a.aggregate_parent else []):
                status = pathlib.Path(f'/proc/{pid}/status').read_text()
                rss += int(status.split('VmRSS:')[1].split()[0])*1024
            if int(pathlib.Path('/proc/meminfo').read_text().split('SwapTotal:')[1].split()[0]):
                stop=stop or 'swap-enabled'
            peak_aggregate = max(peak_aggregate, rss)
            max_lean_processes = max(max_lean_processes, lean_processes)
            if rss > 12*1024**3: stop=stop or 'aggregate-rss'
            if lean_processes > 1: stop=stop or 'parallel-lean'
        if stop:
            if not a.aggregate:
                os.killpg(proc.pid,signal.SIGTERM)
                try: proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid,signal.SIGKILL); proc.wait()
            break
        time.sleep(.25)
    # A completed child is not evidence of meeting an already expired deadline.
    if original_parent is not None and os.getppid()!=original_parent:
        stop=stop or 'parent-lost'
    if a.aggregate and time.monotonic()-start>a.seconds:
        stop=stop or 'timeout'
except BaseException as error:
    if not a.aggregate:
        raise
    stop=stop or ('parent-lost' if original_parent is not None and os.getppid()!=original_parent else 'monitor-error')
    monitor_error=type(error).__name__ + ': ' + str(error)
finally:
    if a.aggregate:
        # Signals must not interrupt cleanup of an owned live process group.
        for signum in handlers:
            signal.signal(signum, signal.SIG_IGN)
        try:
            if proc is not None:
                if proc.poll() is None:
                    try: os.killpg(proc.pid,signal.SIGTERM)
                    except ProcessLookupError: pass
                    try: proc.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        try: os.killpg(proc.pid,signal.SIGKILL)
                        except ProcessLookupError: pass
                        proc.wait()
                else:
                    proc.wait()
                try: os.killpg(proc.pid,0)
                except ProcessLookupError: pass
                else:
                    os.killpg(proc.pid,signal.SIGKILL)
                    stop=stop or 'surviving-process-group'
        finally:
            for signum, handler in handlers.items():
                signal.signal(signum, handler)
if not a.aggregate:
    # Preserve the frozen v1 route's existing cleanup/default records.
    try: os.killpg(proc.pid,0)
    except ProcessLookupError: pass
    else:
        os.killpg(proc.pid,signal.SIGKILL)
        stop=stop or 'surviving-process-group'
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
record=dict(command=cmd,exit=proc.returncode if proc is not None else None,stop=stop,wall_seconds=time.monotonic()-start,
            cpu_seconds=usage.ru_utime+usage.ru_stime,max_rss_kib=usage.ru_maxrss,
            requested_threads=1,per_process_address_space_bytes=12*1024**3,headroom_bytes=4*1024**3,
            rss_measurement='RUSAGE_CHILDREN high-water; not aggregate RSS')
if a.aggregate:
    record.update(peak_sampled_aggregate_rss=peak_aggregate, max_lean_processes=max_lean_processes,
                  aggregate_rss_limit_bytes=12*1024**3, no_swap_required=True,
                  requested_seconds=a.seconds, polling_seconds=.25, termination_grace_seconds=5,
                  monitor_error=monitor_error, original_parent_pid=original_parent,
                  aggregate_scope='Lean tree + monitor' + (' + serial v2 driver' if a.aggregate_parent else ''))
a.record.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
raise SystemExit(1 if stop else proc.returncode)
