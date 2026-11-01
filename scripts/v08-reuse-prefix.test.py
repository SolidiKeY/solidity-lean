#!/usr/bin/env python3
"""Inspect-only corruption tests; never starts Docker or executes the driver."""
import ast, copy, hashlib, json, os, types
from pathlib import Path
root=Path(__file__).resolve().parent.parent
tree=ast.parse((root/'scripts/v08-reuse-prefix.py').read_text())
function=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='inspect_reuse')
fmt_node=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='fmt' for t in n.targets))
fmt=ast.literal_eval(fmt_node.value)
seed=Path('/workspace/v08-world-lowering-evidence/v08-gate-718396-d77b835d.json')
previous=json.loads(seed.read_text())
# The guard's positive fixture belongs to the historical pinned worktree.
# Bind immutable bytes explicitly; never pick a fixture by mutable mtime.
record=seed.parent/'prefix-reuse-v08-gate-841312-91187aee-before.json'
assert hashlib.sha256(record.read_bytes()).hexdigest()=='e14ab26a13ede5931950da81dbd030dfde39ef536b115d3c5a9ddc6ee6fbd730'
fixture_root=Path(previous['repository'])
assert str(fixture_root)=='/workspace/v08-world-lowering-pinned'
baseline=json.loads(record.read_text())['inspection']
current=[baseline]
calls=[]
def fake(args,**kwargs):
 assert kwargs['env']=={'SAFE':'1'} and 'inspect' in args and 'start' not in args
 calls.append(args)
 return json.dumps(current[0])
ns=dict(json=json,subprocess=types.SimpleNamespace(check_output=fake),previous=previous,
 root=fixture_root,os=os,seed=seed,seed_hash=hashlib.sha256(seed.read_bytes()).hexdigest(),
 hashlib=hashlib,Path=Path,fmt=fmt)
exec(compile(ast.Module(body=[function],type_ignores=[]),'inspector-test','exec'),ns)
check=ns['inspect_reuse']
check(['docker'],{'SAFE':'1'})
# The historical record must not be accepted under the present worktree context.
ns['root']=root
try:
 check(['docker'],{'SAFE':'1'})
except AssertionError:
 pass
else:
 raise AssertionError('accepted historical profile under current worktree context')
ns['root']=fixture_root
cases=[('active','running',True),('foreign-token','token','wrong'),
 ('raised-memory','memory',13*1024**3),('swap','swap_total',13*1024**3),
 ('cpu','cpu_nano',2000000000),('network','network','host'),
 ('wrong-image','image','wrong'),('changed-cmd','cmd',['sh','-c','true']),
 ('wrong-workdir','workdir','/tmp'),('wrong-user','user','0:0'),
 ('wrong-driver','driver','overlay2'),('root-write','writable_bytes',1),
 ('missing-mount','mounts',[]),
 ('cache-env','selected_env',[None,'LAKE_CACHE_DIR=wrong','LAKE_ARTIFACT_CACHE=false','LEAN_NUM_THREADS=1'])]
for name,key,value in cases:
 current[0]=copy.deepcopy(baseline)
 current[0][key]=value
 try:
  check(['docker'],{'SAFE':'1'})
 except AssertionError:
  pass
 else:
  raise AssertionError('accepted '+name)
assert len(calls)==16
print('PASS: SHA-bound historical positive accepted;current-context mismatch and14 original corrupt/foreign/unbounded profiles rejected;16 mocked inspect-only calls;no Docker start/build/write')
