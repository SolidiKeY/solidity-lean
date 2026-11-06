#!/usr/bin/env python3
"""Serial incremental compatibility survey; never a clean timing gate."""
import argparse, fcntl, json, os, resource, subprocess
from pathlib import Path
from census import census
from bounded import run, available, settings, passed
ap=argparse.ArgumentParser(); ap.add_argument('--toolchain',type=Path,required=True); ap.add_argument('--lib',type=Path,required=True); ap.add_argument('--out',type=Path,required=True); ap.add_argument('--only',action='append'); a=ap.parse_args()
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','w'); fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
if int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('SwapTotal:'))): raise SystemExit('SWAP_BLOCK')
data=census(Path.cwd())
if a.only and not set(a.only).issubset(data['build_order']): raise SystemExit('UNKNOWN_MODULE: '+str(sorted(set(a.only)-set(data['build_order']))))
a.out.mkdir(parents=True,exist_ok=False); (a.out/'census.json').write_text(json.dumps(data,indent=2))
env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(a.lib.resolve())); rows=[]; failed=set()
lean=str(a.toolchain.resolve()/'bin/lean'); version=subprocess.check_output([lean,'--version'],text=True).strip()
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
        cmd=[lean,'-j1','--tstack=131072','-o',str(dst),str(src)]
        result=run(cmd,log=a.out/(mod+'.log'),env=env)
        row={'module':mod,'status':'pass' if passed(result) else 'fail','command':cmd,**result}
        if not passed(result): failed.add(mod)
    rows.append(row); (a.out/'summary.json').write_text(json.dumps({'boundary':'Incremental compatibility survey; not clean timing or final acceptance','lean':version,'settings':settings(),'only':a.only,'cumulative_peak_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'rows':rows},indent=2)); print(mod,row['status'],flush=True)

raise SystemExit(1 if failed else 0)
