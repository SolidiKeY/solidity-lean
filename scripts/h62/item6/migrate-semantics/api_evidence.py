#!/usr/bin/env python3
"""Compile pinned-base ABI sources then export/compare five elaborated ABI APIs."""
import argparse, fcntl, hashlib, json, os, resource, signal, subprocess, time
from pathlib import Path
ap=argparse.ArgumentParser(); ap.add_argument('--out',type=Path,required=True); a=ap.parse_args()
root=Path.cwd(); out=a.out.resolve(); out.mkdir(parents=True,exist_ok=False)
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','w'); fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
if int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('SwapTotal:'))): raise SystemExit('SWAP_BLOCK')
base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'; evidence=Path('/workspace/h62-migrate-semantics-evidence')
old=Path('/workspace/.setup/tools/lean-4.24.0-linux'); new=evidence/'lean-4.35.0-linux'
original=out/'base'; original.mkdir(); original_lib=original/'lib'; original_lib.mkdir(); rows=[]
def available():
    host=int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')))*1024
    cap=Path('/sys/fs/cgroup/memory.max').read_text().strip(); used=int(Path('/sys/fs/cgroup/memory.current').read_text())
    return min(host,int(cap)-used) if cap!='max' else host
def limits(): resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
def run(label,cmd,cwd,env):
    if available()<4*1024**3: raise SystemExit('RESOURCE_BLOCK')
    t=time.monotonic(); stop=None
    with (out/(label+'.log')).open('w') as f:
        p=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits,start_new_session=True)
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
    rows.append({'label':label,'command':cmd,'cwd':str(cwd),'exit':p.returncode,'stop':stop,'wall_seconds':time.monotonic()-t})
    (out/'commands.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(label,p.returncode,flush=True)
    if p.returncode: raise SystemExit(p.returncode)
env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(original_lib)+os.pathsep+str(evidence/'old-clean-02/lib'))
source_hashes={}
for name in ['AbiEntry','AbiAccess','AbiAccessChecks','AbiEntryChecks','AbiEntryProofs']:
    rel=Path('Solidity/Semantics')/(name+'.lean'); src=original/rel; dst=original_lib/rel.with_suffix('.olean')
    src.parent.mkdir(parents=True,exist_ok=True); dst.parent.mkdir(parents=True,exist_ok=True)
    raw=subprocess.check_output(['git','show',base+':'+str(rel)]); src.write_bytes(raw); source_hashes[str(rel)]=hashlib.sha256(raw).hexdigest()
    run('base-'+name,[str(old/'bin/lean'),'-j1','--tstack=131072','-o',str(dst),str(rel)],original,env)
helper=root/'tests/h62/item6/migrate-semantics/ExportAbiTypes.lean'
clean=evidence/'new-clean-h76-01'; build=json.loads((clean/'summary.json').read_text()); snapshot=json.loads((clean/'census.json').read_text())
new_version=subprocess.check_output([str(new/'bin/lean'),'--version'],text=True).strip()
if build['versions']['lean']!=new_version: raise SystemExit('NEW_TOOLCHAIN_PROVENANCE_MISMATCH')
new_hashes={}; olean_hashes={}
for rel,old_hash in source_hashes.items():
    actual=hashlib.sha256((root/rel).read_bytes()).hexdigest(); mod=rel[:-5].replace('/','.')
    if snapshot['closure_sha256'][mod]!=actual: raise SystemExit('NEW_SOURCE_PROVENANCE_MISMATCH: '+rel)
    if not any(r['module']==mod and r['exit']==0 for r in build['rows']): raise SystemExit('NO_SUCCESSFUL_NEW_BUILD: '+mod)
    new_hashes[rel]=actual; olean_hashes[mod]=hashlib.sha256((clean/'lib'/Path(rel).with_suffix('.olean')).read_bytes()).hexdigest()

for label,tc,lib in [('old',old,env['LEAN_PATH']),('new',new,str(evidence/'new-clean-h76-01/lib'))]:
    local=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=lib,H62_API_OUTPUT=str(out/(label+'-types.json')))
    run(label+'-types',[str(tc/'bin/lean'),'-j1','--tstack=131072',str(helper)],root,local)
def read(label):
    rows=json.loads((out/(label+'-types.json')).read_text())
    if 'UNSUPPORTED_' in json.dumps(rows): raise SystemExit('UNSUPPORTED_EXPRESSION')
    result={r['name']:r for r in rows}
    if len(result)!=len(rows): raise SystemExit('DUPLICATE_NAME')
    return result
before=read('old'); after=read('new'); same=[]; changed=[]
for name in sorted(before.keys()&after.keys()):
    (same if before[name]==after[name] else changed).append(name)
def digest(d): return hashlib.sha256(json.dumps(d,sort_keys=True,separators=(',',':')).encode()).hexdigest()
report={'base':base,'source_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'base_source_sha256':source_hashes,'new_source_sha256':new_hashes,'new_olean_sha256':olean_hashes,'exporter_sha256':hashlib.sha256(helper.read_bytes()).hexdigest(),'new_build_census_sha256':hashlib.sha256((clean/'census.json').read_bytes()).hexdigest(),'new_lean':new_version,'old_lean':subprocess.check_output([str(old/'bin/lean'),'--version'],text=True).strip(),'boundary':'Elaborated type syntax comparison for five ABI modules only; binder names/metadata ignored, private names excluded. Includes compiler-generated constants. Not all 82 modules or definitional-equivalence checking.','old_count':len(before),'new_count':len(after),'old_sha256':digest(before),'new_sha256':digest(after),'equal':same,'changed':changed,'removed':sorted(before.keys()-after.keys()),'added':sorted(after.keys()-before.keys())}
report['status']='differences' if changed or report['removed'] or report['added'] else 'equal'
report['compatibility_gate']='fail' if report['status']=='differences' else 'subset_equal'
(out/'comparison.json').write_text(json.dumps(report,indent=2)+'\n'); print('API equal',len(same),'changed',len(changed),'removed',len(report['removed']),'added',len(report['added']))

raise SystemExit(1 if report['status']=='differences' else 0)
