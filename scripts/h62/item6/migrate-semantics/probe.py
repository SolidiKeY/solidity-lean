#!/usr/bin/env python3
"""Serial incremental compatibility survey; never a clean timing gate."""
import argparse, fcntl, json, os, resource, signal, subprocess, time
from pathlib import Path
from census import census
ap=argparse.ArgumentParser(); ap.add_argument('--toolchain',type=Path,required=True); ap.add_argument('--lib',type=Path,required=True); ap.add_argument('--out',type=Path,required=True); ap.add_argument('--only',action='append'); a=ap.parse_args()
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','w'); fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
if int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('SwapTotal:'))): raise SystemExit('SWAP_BLOCK')
data=census(Path.cwd())
if a.only and not set(a.only).issubset(data['build_order']): raise SystemExit('UNKNOWN_MODULE: '+str(sorted(set(a.only)-set(data['build_order']))))
a.out.mkdir(parents=True,exist_ok=False); (a.out/'census.json').write_text(json.dumps(data,indent=2))
env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(a.lib.resolve())); rows=[]; failed=set()
lean=str(a.toolchain.resolve()/'bin/lean'); version=subprocess.check_output([lean,'--version'],text=True).strip()
def limits(): resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
def available():
    host=int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')))*1024
    cap=Path('/sys/fs/cgroup/memory.max').read_text().strip(); used=int(Path('/sys/fs/cgroup/memory.current').read_text())
    return min(host,int(cap)-used) if cap!='max' else host
for mod in data['build_order']:
    if a.only and mod not in a.only: continue
    src=Path(mod.replace('.','/')+'.lean'); dst=a.lib/src.with_suffix('.olean'); dst.parent.mkdir(parents=True,exist_ok=True)
    # Existing outputs were produced locally with this pinned toolchain; this
    # survey deliberately rebuilds every module rather than trusting freshness.
    import re
    from census import strip_comments
    deps=re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)',strip_comments(src.read_text()),re.M)
    blocked=sorted(set(deps)&failed)
    if blocked:
        failed.add(mod); row={'module':mod,'status':'dependency_blocked','dependencies':blocked}
    elif available()<4*1024**3:
        row={'module':mod,'status':'RESOURCE_BLOCK'}; failed.add(mod)
    else:
        cmd=[lean,'-j1','--tstack=131072','-o',str(dst),str(src)]; t=time.monotonic(); stop=None
        with (a.out/(mod+'.log')).open('w') as f:
            p=subprocess.Popen(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits,start_new_session=True)
            try:
                while p.poll() is None:
                    if available()<4*1024**3 or time.monotonic()-t>300:
                        stop='RESOURCE_BLOCK' if available()<4*1024**3 else 'MODULE_300S_STOP'
                        try: os.killpg(p.pid,signal.SIGKILL)
                        except ProcessLookupError: pass
                        p.wait(); break
                    time.sleep(.25)
            finally:
                if p.poll() is None:
                    try: os.killpg(p.pid,signal.SIGKILL)
                    except ProcessLookupError: pass
                    p.wait()
        row={'module':mod,'status':'pass' if p.returncode==0 else 'fail','exit':p.returncode,'stop':stop,'wall_seconds':time.monotonic()-t,'command':cmd}
        if p.returncode: failed.add(mod)
    rows.append(row); (a.out/'summary.json').write_text(json.dumps({'boundary':'Incremental compatibility survey; not clean timing or final acceptance','lean':version,'only':a.only,'cumulative_peak_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'rows':rows},indent=2)); print(mod,row['status'],flush=True)

raise SystemExit(1 if failed else 0)
