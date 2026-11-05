import hashlib,json,pathlib,subprocess,sys,time
root=pathlib.Path('tests/calldata-packets-1105/RawBool/evidence');stateFile=root/'prepare-state.json';plan=[];seen=set()
def visit(module):
 if module in seen:return
 seen.add(module);path=pathlib.Path(module.replace('.','/')+'.lean')
 if not path.exists():return
 for line in path.read_text().splitlines():
  if line.startswith('import '):
   for dep in line.split()[1:]:visit(dep)
 plan.append(module)
visit('Solidity.Backend.MemoryOps.SourceRawBoolEntry')
state=json.loads(stateFile.read_text()) if stateFile.exists() else dict(next=0,modules=plan)
assert state['modules']==plan
start=time.monotonic()
for i in range(state['next'],len(plan)):
 remaining=int(290-(time.monotonic()-start))
 if remaining<2:print('PREPARATION_GROUP_BOUND',i,len(plan),flush=True);raise SystemExit(3)
 module=plan[i];label='dep-'+module.replace('.','_')
 result=subprocess.run(['python3','tests/calldata-packets-1105/RawBool/run.py',label,str(min(180,remaining)),'lake','build','+'+module+':olean'],text=True,capture_output=True)
 if result.returncode:
  print(result.stdout+result.stderr,flush=True);raise SystemExit(result.returncode)
 state['next']=i+1;stateFile.write_text(json.dumps(state,indent=2)+'\n')
 if (i+1)%10==0 or i+1==len(plan):print('PREPARED',i+1,len(plan),module,flush=True)
 record=json.loads(sorted(root.glob(label+'-*.json'))[-1].read_text())
 if record['above_60_seconds']:print('MODULE_ABOVE_60_SECONDS',module,record['wall_seconds'],flush=True)
print('PREREQUISITE_CLOSURE_PASS',len(plan),flush=True)
