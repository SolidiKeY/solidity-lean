#!/usr/bin/env python3
"""Memory-controller diagnostic of the pinned-base blocked prerequisite, not a full build."""
import argparse,fcntl,hashlib,json,os,resource,subprocess
from pathlib import Path
from bounded import run,settings,passed,cap_kind
ap=argparse.ArgumentParser(); ap.add_argument('--out',type=Path,required=True); a=ap.parse_args()
lock=open('/h78-writer.lock','r'); fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
if cap_kind()!='cgroup': raise SystemExit('CGROUP_MODE_REQUIRED')
out=a.out; out.mkdir(parents=True,exist_ok=False)
source=Path('/workspace/h62-migrate-semantics-base-8g'); previous=Path('/workspace/h62-migrate-semantics-evidence/old-clean-h78-01')
snapshot=json.loads((previous/'census.json').read_text())
if snapshot['head']!='c6f550e281a7e5affa9a99bc2cdaed556dec00e4': raise SystemExit('BASE_MISMATCH')
for module,h in snapshot['closure_sha256'].items():
    if hashlib.sha256((source/(module.replace('.','/')+'.lean')).read_bytes()).hexdigest()!=h: raise SystemExit('SOURCE_MISMATCH:'+module)
old=Path('/workspace/.setup/tools/lean-4.24.0-linux'); rows=[]
versions={k:subprocess.check_output([str(old/'bin'/k),'--version'],text=True).strip() for k in ['lean','lake']}
for module in ['Solidity.KeySort','Solidity.Source.Horizon']:
    rel=Path(module.replace('.','/')+'.lean'); target=out/(module+'.olean')
    command=[str(old/'bin/lean'),'-j1','--tstack=131072','-o',str(target),str(rel)]
    result=run(command,cwd=source,env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(previous/'lib')),log=out/(module+'.log'))
    rows.append({'module':module,'command':command,**result})
    report={'boundary':'Isolated pinned-base prerequisite check using already-built original dependency artifacts. Not a clean build or timing comparison.','base':snapshot['head'],'versions':versions,'runtime_image':os.environ.get('H78_RUNTIME_IMAGE'),'settings':settings(),'inherited_rlimit_as':resource.getrlimit(resource.RLIMIT_AS),'rows':rows,'cgroup_memory_peak_bytes':int(Path('/sys/fs/cgroup/memory.peak').read_text()),'cgroup_memory_events':Path('/sys/fs/cgroup/memory.events').read_text()}
    (out/'result.json').write_text(json.dumps(report,indent=2)+'\n'); print(module,result['exit'],result['stop'],flush=True)
    if not passed(result): raise SystemExit(1)
