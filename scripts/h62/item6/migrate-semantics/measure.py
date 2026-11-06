#!/usr/bin/env python3
"""Clean serial closure diagnostic. Does not replace repository final gates."""
import argparse, fcntl, hashlib, json, os, resource, subprocess, time
from pathlib import Path
from census import census
ap=argparse.ArgumentParser(); ap.add_argument('--toolchain',type=Path,required=True); ap.add_argument('--out',type=Path,required=True); a=ap.parse_args()
root=Path.cwd(); out=a.out.resolve()
if int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('SwapTotal:'))): raise SystemExit('SWAP_BLOCK: swap must be unavailable')
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','w'); fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
if subprocess.check_output(['git','status','--porcelain','--untracked-files=all','--','Solidity'],text=True): raise SystemExit('source changes require new frozen snapshot')
if out.exists(): raise SystemExit('refuse warm output; choose a new directory')
out.mkdir(parents=True); artifacts=out/'lib'; artifacts.mkdir(); data=census(root)
(out/'census.json').write_text(json.dumps(data,indent=2)+'\n')
env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(artifacts)); env.pop('LEAN_SRC_PATH',None)
lean=str(a.toolchain.resolve()/'bin/lean'); lake=str(a.toolchain.resolve()/'bin/lake')
versions={x:subprocess.check_output([p,'--version'],text=True).strip() for x,p in [('lean',lean),('lake',lake)]}
start=time.monotonic(); rows=[]
(out/'summary.json').write_text(json.dumps({'complete':False,'stop':'INITIALIZING','versions':versions}))
def limits(): resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
def available():
    host=int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')))*1024
    cg=Path('/sys/fs/cgroup'); cap=(cg/'memory.max').read_text().strip(); used=int((cg/'memory.current').read_text())
    return min(host,int(cap)-used) if cap!='max' else host
order=data['build_order']
if 'Solidity.KeySort' in order: order=['Solidity.KeySort']+[m for m in order if m!='Solidity.KeySort']
for mod in order:
    if available()<4*1024**3:
        (out/'summary.json').write_text(json.dumps({'complete':False,'stop':'RESOURCE_BLOCK','rows':rows}))
        raise SystemExit('RESOURCE_BLOCK: less than 4 GiB headroom')
    rel=Path(mod.replace('.','/')); target=artifacts/rel.with_suffix('.olean'); target.parent.mkdir(parents=True,exist_ok=True)
    cmd=[lean,'-j1','--tstack=131072','-o',str(target),str(rel.with_suffix('.lean'))]
    log=out/(mod+'.log'); t=time.monotonic()
    with log.open('w') as f:
        proc=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,start_new_session=True)
        reason=None
        try:
            while proc.poll() is None:
                if available()<4*1024**3 or time.monotonic()-t>300:
                    import signal
                    reason='RESOURCE_BLOCK' if available()<4*1024**3 else 'MODULE_300S_STOP'
                    try: os.killpg(proc.pid,signal.SIGKILL)
                    except ProcessLookupError: pass
                    proc.wait(); break
                time.sleep(.25)
        finally:
            if proc.poll() is None:
                import signal
                try: os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError: pass
                proc.wait()
    row={'cumulative_peak_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'module':mod,'command':cmd,'exit':proc.returncode,'wall_seconds':time.monotonic()-t,'stop':reason}; rows.append(row)
    summary={'versions':versions,'source_head':data['head'],'boundary':'Clean serial Lean closure diagnostic; final run-lean.sh and KeySort gates separate.', 'settings':{'threads':1,'address_space_bytes':12*1024**3,'reserve_bytes':4*1024**3,'module_timeout_seconds':300,'swap_total':next(s for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('SwapTotal:'))},'rows':rows,'wall_seconds':time.monotonic()-start,'complete':len(rows)==len(data['build_order']) and all(r['exit']==0 for r in rows)}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n'); print(mod,proc.returncode,flush=True)
    if proc.returncode: raise SystemExit(1)
