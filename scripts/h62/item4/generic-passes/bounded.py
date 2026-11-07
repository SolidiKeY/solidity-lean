#!/usr/bin/env python3
"""Bounded direct Lean only. Per-process hard 12 GiB address-space cap,
sampled aggregate RSS cap, host+cgroup 4 GiB available reserve, no host swap.
No systemd, v4.24 cache, or unrelated process termination. Explicit Lean -j1.
"""
import argparse, fcntl, json, os, resource, signal, subprocess, time
from pathlib import Path
p=argparse.ArgumentParser(); p.add_argument('label'); p.add_argument('arguments',nargs='+'); a=p.parse_args()
from runtime_paths import EVIDENCE as evidence
evidence.mkdir(parents=True,exist_ok=True)
lean=evidence/'toolchain/lean-4.35.0-linux/bin/lean'
if '-j1' not in a.arguments: raise SystemExit('explicit -j1 required')
if any(x in a.label for x in '/.'): raise SystemExit('simple unique label required')
command=[str(lean),*a.arguments]
lock=Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
lock.parent.mkdir(exist_ok=True); handle=lock.open('a'); fcntl.flock(handle,fcntl.LOCK_EX|fcntl.LOCK_NB)
subprocess.run(['git','status','--short'],check=True)
if len(Path('/proc/swaps').read_text().splitlines())!=1: raise SystemExit('swap present')
env=os.environ.copy(); env['LEAN_NUM_THREADS']='1'
env['PATH']=str(lean.parent)+':'+env['PATH']
env['XDG_CACHE_HOME']=str(evidence/'cache-v4.35.0')
env['LEAN_PATH']=str(evidence/'build-v4.35.0')
def limit(): resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
def available():
    host=int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))
    cap=Path('/sys/fs/cgroup/memory.max').read_text().strip()
    if cap!='max':
        current=int(Path('/sys/fs/cgroup/memory.current').read_text())
        host=min(host,(int(cap)-current)//1024)
    return host
def members(group):
    result=[]
    for stat in Path('/proc').glob('[0-9]*/stat'):
        try:
            fields=stat.read_text().rsplit(')',1)[1].split()
            if int(fields[2])==group and fields[0]!='Z':
                result.append((int(stat.parent.name),int(fields[21])*os.sysconf('SC_PAGE_SIZE')//1024))
        except (FileNotFoundError,ProcessLookupError,PermissionError): pass
    return result
log=evidence/(a.label+'.log'); record=evidence/(a.label+'.json')
if log.exists() or record.exists(): raise SystemExit('preserve existing evidence; choose fresh label')
if available()<4*1024**2: raise SystemExit('insufficient available reserve')
start=time.monotonic(); peak=0; stopped=None; job=None; code=1
try:
    with log.open('w') as output:
        job=subprocess.Popen(command,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limit)
        while True:
            code=job.poll(); owned=members(job.pid); rss=sum(x[1] for x in owned)
            peak=max(peak,rss)
            if code is not None and not owned: break
            if rss>12*1024**2 or available()<4*1024**2:
                stopped='resource guard'; break
            if code is not None and owned:
                stopped='leader exited with descendants'; break
            time.sleep(.2)
except BaseException as error:
    stopped=type(error).__name__+': '+str(error)
finally:
    if job is not None:
        if members(job.pid):
            try: os.killpg(job.pid,signal.SIGKILL)
            except ProcessLookupError: pass
        code=job.wait()
        deadline=time.monotonic()+5
        while members(job.pid) and time.monotonic()<deadline: time.sleep(.1)
        if members(job.pid): stopped='owned descendants remain after kill'
    result=dict(command=command,exit=code,elapsed_seconds=time.monotonic()-start,peak_group_rss_kib=peak,
        stopped=stopped,threads=1,per_process_address_cap_gib=12,sampled_group_rss_cap_gib=12,
        host_and_cgroup_reserve_gib=4,swap='absent',log=str(log))
    record.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result))
raise SystemExit(code if code and code>0 else (1 if stopped or code is None or code<0 else 0))
