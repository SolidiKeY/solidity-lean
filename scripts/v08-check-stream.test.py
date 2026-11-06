#!/usr/bin/env python3
"""Run EVERY existing corruption case unchanged, streaming its exact JSON input.
No checker/guard/case/expected-result changes. Persist seed+delta+expanded SHA
and raw checker output; no source/cache/evidence deletion or temporary full copies.
"""
import ast,copy,hashlib,json,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parent.parent
script=root/'scripts/v08-check.test.py'
assert len(sys.argv)==2
seed_path=Path(sys.argv[1]);seed_sha=hashlib.sha256(seed_path.read_bytes()).hexdigest()
source=script.read_text();tree=ast.parse(source)
replacement=ast.parse(r"""
def check(name,result,expected):
 def delta(before,after,path=()):
  if isinstance(before,dict) and isinstance(after,dict):
   out=[]
   for key in sorted(set(before)|set(after)):
    if key not in after:out.append(dict(path=list(path+(key,)),remove=True))
    elif key not in before:out.append(dict(path=list(path+(key,)),value=after[key]))
    else:out.extend(delta(before[key],after[key],path+(key,)))
   return out
  return [] if type(before) is type(after) and before==after else [dict(path=list(path),value=after)]
 changes=delta(original,result)
 replay=copy.deepcopy(original)
 for change in changes:
  parent=replay
  for key in change['path'][:-1]:parent=parent[key]
  if change.get('remove'):parent.pop(change['path'][-1])
  else:parent[change['path'][-1]]=change['value']
 assert replay==result,'delta replay differs'
 payload=json.dumps(result,indent=2)+'\n'
 assert json.dumps(replay,indent=2)+'\n'==payload,'expanded JSON replay bytes differ'
 manifest=dict(seed=str(seed_path),seed_sha256=seed_sha,delta=changes,
  expanded_sha256=hashlib.sha256(payload.encode()).hexdigest(),expected_pass=expected,
  command=[sys.executable,str(checker),'/dev/stdin'])
 (fixtures/(name+'.input.json')).write_text(json.dumps(manifest,indent=2)+'\n')
 proc=subprocess.run(manifest['command'],input=payload,cwd=root,text=True,
  stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (fixtures/(name+'.log')).write_text('exit='+str(proc.returncode)+'\n'+proc.stdout)
 assert (proc.returncode==0)==expected,(name,proc.stdout)
""").body[0]
functions=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='check']
assert len(functions)==1
# Only the input/storage plumbing function changes. ALL original case statements,
# mutations and expected outcomes execute byte-for-byte from the original AST.
original_cases=ast.dump(ast.Module(body=[n for n in tree.body if n is not functions[0]],type_ignores=[]))
tree.body[tree.body.index(functions[0])]=replacement
assert ast.dump(ast.Module(body=[n for n in tree.body if n is not replacement],type_ignores=[]))==original_cases
ns=dict(__file__=str(script),__name__='__main__',copy=copy,hashlib=hashlib,
 seed_path=seed_path,seed_sha=seed_sha)
exec(compile(ast.fix_missing_locations(tree),str(script),'exec'),ns)
files=sorted(ns['fixtures'].glob('*.input.json'))
assert len(files)>=36 and sum(json.loads(p.read_text())['expected_pass'] for p in files)==1
print('PASS: ALL '+str(len(files))+' existing cases; exact streamed production-checker inputs; replayable deltas/SHA; fixtures='+str(ns['fixtures']))
