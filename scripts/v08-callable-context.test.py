#!/usr/bin/env python3
"""Additive current-public caller-context certificate integrity, no Lean/Docker."""
import copy, hashlib, json, pathlib, re, runpy, subprocess, sys
ROOT=pathlib.Path(__file__).resolve().parent.parent
OLD=runpy.run_path(str(ROOT/'scripts/v08-assigned-callable.test.py'),run_name='preserved_assigned_checker')
FILE=OLD['FILE'];BASE='8a5ffa2081d43c59942ad21907da63cff4f54117'
PUBLIC='24149fd567ec273e5c72760ecf0a25a940c4c4fc'
NS='Solidity.Lowering.V08.AssignedCallableContext.'
NAMES=set('transport initial_alignment client actual_vector wrong_source_snapshot corrupt_live_run wrong_live_binding corrupt_actual closed_client'.split())
def digest(b):return hashlib.sha256(b).hexdigest()
def validate(source,before,result,log,bindings):
 OLD['validate'](source,before,result,log,bindings)
 policy=json.loads((ROOT/'scripts/v08-published-bindings.json').read_text())
 assert before['peer']==policy and policy['published_head']==PUBLIC
 assert before['controls'][str(ROOT/'scripts/v08-published-bindings.json')]==digest((ROOT/'scripts/v08-published-bindings.json').read_bytes())
 text=source.decode();prefix=text.split('/-! Reached caller alignment for actual assignment-argument execution.')[0]
 old=subprocess.check_output(['git','show',BASE+':'+FILE],cwd=ROOT).decode()
 assert prefix.rstrip()==old.rstrip(),'full predecessor source/guards preserved'
 found=re.findall(r"/-- info: '"+re.escape(NS)+r"(\w+)' depends on axioms: \[([^\]]*)\] -/\s*#guard_msgs in\s*#print axioms "+re.escape(NS)+r"\1",text)
 assert len(found)==len(NAMES) and {n for n,_ in found}==NAMES
 assert all(set(re.findall(r'[\w.]+',a))=={'propext','Classical.choice','Quot.sound'} for _,a in found)
 producer='Solidity/Lowering/V07/ContextMapWrite.lean';data=subprocess.check_output(['git','show',PUBLIC+':'+producer],cwd=ROOT)
 assert data==(ROOT/producer).read_bytes() and before['source'][producer]==digest(data)
def main():
 run=pathlib.Path(sys.argv[1]);source=(ROOT/FILE).read_bytes();before=json.loads((run/'before.json').read_text());result=json.loads((run/'result.json').read_text());log=(run/'build.log').read_bytes();bindings=json.loads((run/'log-bindings.json').read_text())
 validate(source,before,result,log,bindings);count=0
 def reject(s=source,b=before,r=result,l=log,k=bindings):
  nonlocal count
  try:validate(s,b,r,l,k)
  except AssertionError:count+=1;return
  raise AssertionError('corruption accepted')
 reject(s=source+b' ')
 for key,value in [('actual_exit',1),('source_and_controls_checked',False)]:
  bad=copy.deepcopy(result);bad[key]=value;reject(r=bad)
 bad=copy.deepcopy(before);bad['peer']['published_head']=OLD['PUBLIC'];reject(b=bad)
 bad=copy.deepcopy(before);bad['source']['Solidity/Lowering/V07/ContextMapWrite.lean']='0'*64;reject(b=bad)
 bad=copy.deepcopy(before);bad['controls']['/workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102/coord-access/current-file.txt']=digest(b'wrong file\n');reject(b=bad)
 for old,new in [
  (b'#guard_msgs in\n#print axioms '+NS.encode()+b'transport',b'#print axioms '+NS.encode()+b'transport'),
  (b"'"+NS.encode()+b"closed_client' depends on axioms: [propext,",b"'"+NS.encode()+b"closed_client' depends on axioms: [sorryAx,"),
  (b'Environment/context/width-polymorphic assignment-argument application.',b'Environment/context/width-polymorphic WRONG assignment-argument application.'),
 ]:
  altered=source.replace(old,new);assert altered!=source;bad=copy.deepcopy(before);bad['source'][FILE]=digest(altered);reject(s=altered,b=bad)
 print(f'PASS exact9 new +31 predecessor guards, old full source and current-public ContextMap/source/target/run bindings; {count} corruptions; no Lean/Docker')
if __name__=='__main__':main()
