#!/usr/bin/env python3
"""Bounded caller's private source/olean harness; no shared root registration.
Run under `lake env python3 .../kernel.py`; each Lean process is serial -j1.
Own imports must resolve to this harness's private oleans, never stale Lake ones.
"""
import argparse,hashlib,json,os,pathlib,re,subprocess,sys,time
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[2]
SOURCE=HERE/'lean'
LIB=HERE/'runtime/build/lib'
INDEX=HERE/'runtime/build/index.json'
PREFIX='Solidity.Assurance.NonVacuityH28.'
p=argparse.ArgumentParser();p.add_argument('--all',action='store_true');p.add_argument('--module',action='append',default=[]);p.add_argument('--fresh',action='store_true');a=p.parse_args()
files={PREFIX+f.stem:f for f in (SOURCE/'Solidity/Assurance/NonVacuityH28').glob('*.lean')}
selected=sorted(files) if a.all else a.module
if not selected or any(m not in files for m in selected):p.error('choose --all or existing --module')
assert os.environ.get('LEAN_NUM_THREADS')=='1','bounded caller must set serial threads'
assert os.environ.get('LEAN_PATH'),'invoke through lake env'
LIB.mkdir(parents=True,exist_ok=True)
# Lean selects a top-level namespace directory before individual modules.
# Mirror baseline namespace entries as explicit symlinks, excluding all stale
# copies of our own namespace; only our newly checked oleans may populate it.
baseline=ROOT/'.lake/build/lib/lean'
assert str(baseline) in os.environ['LEAN_PATH'].split(os.pathsep),'unexpected baseline library path'
def mirror(src,dst,parts=()):
 dst.mkdir(parents=True,exist_ok=True)
 for item in src.iterdir():
  relative=parts+(item.name,)
  if relative==('Solidity','Assurance','NonVacuityH28'):continue
  target=dst/item.name
  if relative in [('Solidity',),('Solidity','Assurance')]:
   if item.is_dir():mirror(item,target,relative)
  elif not target.exists():target.symlink_to(item,target_is_directory=item.is_dir())
mirror(baseline,LIB)

env=dict(os.environ,LEAN_PATH=str(LIB)+os.pathsep+os.environ['LEAN_PATH'])
index=json.loads(INDEX.read_text()) if INDEX.exists() else {}
flags=['-j1','--tstack=131072','--root='+str(SOURCE)]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
script_sha=sha(pathlib.Path(__file__))
seen={};checking=set();records=[]
def visit(module):
 if module in seen:return seen[module]
 assert module not in checking,'cyclic local imports'
 checking.add(module)
 file=files[module]
 imports=re.findall(r'^import (\S+)',file.read_text(),re.M)
 local=[m for m in imports if m.startswith(PREFIX)]
 deps={m:visit(m) for m in local}
 fingerprint=hashlib.sha256(json.dumps([script_sha,sha(file),deps,flags],sort_keys=True).encode()).hexdigest()
 olean=LIB/(module.replace('.','/')+'.olean')
 fresh=a.fresh and module in selected
 if not fresh and olean.exists() and index.get(module,{}).get('fingerprint')==fingerprint and index[module].get('olean_sha256')==sha(olean):
  seen[module]=fingerprint;checking.remove(module);return fingerprint
 olean.parent.mkdir(parents=True,exist_ok=True)
 # --deps resolves actual olean files. Assert private imports before compiling.
 depcmd=['lean',*flags,'--deps',str(file)]
 dep=subprocess.run(depcmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print('H28_DEP_COMMAND '+json.dumps(depcmd),flush=True)
 if dep.returncode:print(dep.stdout,flush=True);raise SystemExit(dep.returncode)
 paths={str(pathlib.Path(line.strip()).resolve()) for line in dep.stdout.splitlines() if line.strip().endswith('.olean')}
 for name in local:
  expected=str(LIB/(name.replace('.','/')+'.olean'))
  assert expected in paths,('local import did not resolve privately',module,name,expected,dep.stdout)
 print('H28_PRIVATE_IMPORTS '+json.dumps(dict(module=module,imports={m:str(LIB/(m.replace('.','/')+'.olean')) for m in local})),flush=True)
 cmd=['lean',*flags,'-o',str(olean),str(file)]
 print('H28_KERNEL_COMMAND '+json.dumps(cmd),flush=True)
 start=time.monotonic();result=subprocess.run(cmd,cwd=ROOT,env=env)
 elapsed=time.monotonic()-start
 if result.returncode:raise SystemExit(result.returncode)
 record=dict(module=module,source=str(file.relative_to(ROOT)),source_sha256=sha(file),fingerprint=fingerprint,olean_sha256=sha(olean),command=cmd,exit=0,elapsed_seconds=elapsed)
 records.append(record);index[module]=record
 INDEX.write_text(json.dumps(index,indent=2)+'\n')
 print('H28_MODULE_PASS '+json.dumps(record),flush=True)
 seen[module]=fingerprint;checking.remove(module);return fingerprint
for module in selected:visit(module)
print('H28_KERNEL_PASS '+json.dumps(dict(requested=selected,compiled=[x['module'] for x in records],source_sha256={str(files[m].relative_to(ROOT)):sha(files[m]) for m in seen},private_lib=str(LIB))),flush=True)
