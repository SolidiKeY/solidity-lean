#!/usr/bin/env python3
"""Run existing imported entry validation via a privately refreshed Lifetime root."""
import json,hashlib,os,subprocess,time,resource,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];BASE=Path(os.environ.get('BASELINE_VALUE_BASE',str(ROOT/'.lake/upstream/value-entry-runtime-20261028'))).resolve();FIXTURE=ROOT/'tests/upstream/baseline-20261028/value-runtime';PIN='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390';COMPILER='/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def fnv(b):
 h=0xcbf29ce484222325
 for v in b:h=((h^v)*0x100000001b3)&((1<<64)-1)
 return hex(h)
def main():
 assert 0<int(Path('/sys/fs/cgroup/memory.max').read_text())<=12*1024**3 and int(Path('/sys/fs/cgroup/memory.swap.max').read_text())==0, 'hard12GiB/no-swap cgroup required'
 assert os.environ.get('LEAN_NUM_THREADS')=='1'
 assert sha(Path(COMPILER))==PIN
 before=json.load(open(BASE/'before.json'));assert all(sha(Path(p))==v for p,v in before['snapshots'].items())
 env={**os.environ,'LEAN_NUM_THREADS':'1','LEAN_PATH':str(BASE/'overlay')+':'+str(ROOT/'.lake/build/lib/lean')};records=[];attempt=os.environ.get('BASELINE_VALUE_ATTEMPT','runtime-final')
 def call(label,cmd,job):
  start=time.monotonic();r=subprocess.run(['timeout','-k','10','120',*cmd],cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log=job/(label+'.log');log.write_bytes(r.stdout);records.append(dict(command=['timeout','-k','10','120',*cmd],exitCode=r.returncode,elapsedSeconds=time.monotonic()-start,log=str(log.relative_to(BASE)),sha256=sha(log),cgroupPeakBytes=int(Path('/sys/fs/cgroup/memory.peak').read_text())));(BASE/(attempt+'-commands.json')).write_text(json.dumps(records,indent=2)+'\n');print(label,r.returncode,flush=True)
  unchanged=all(sha(Path(p))==v for p,v in before['snapshots'].items())
  (job/(label+'-shared-after.json')).write_text(json.dumps(dict(allSharedArtifactsUnchanged=unchanged),indent=2)+'\n')
  assert unchanged,'shared artifact drift'
  if r.returncode:raise SystemExit(r.returncode)
 for mode in ['legacy','viaIR']:
  job=BASE/attempt/mode;job.mkdir(parents=True,exist_ok=False);ast=job/'source.ast.json';source=FIXTURE/'inputs/ValueEntry.sol'
  call('compiler',['node','scripts/solc-ast.mjs','--compiler-file',COMPILER,'--compiler-sha256',PIN,'--source',str(source),'--out',str(ast),'--no-wrapper',*(['--via-ir'] if mode=='viaIR' else [])],job)
  x=json.load(open(ast));assert x['header']['sourceSha256']==sha(source) and x['header']['compilerSha256']==PIN and x['header']['settings']['viaIR']==(mode=='viaIR')
  # The existing API is unbounded Prog.run; exclude looping/assembly syntax here.
  kinds=[]
  def walk(x):
   if isinstance(x,dict):
    if 'nodeType' in x:kinds.append(x['nodeType'])
    for v in x.values():walk(v)
   elif isinstance(x,list):
    for v in x:walk(v)
  walk(x);assert not(set(kinds)&{'ForStatement','WhileStatement','DoWhileStatement','InlineAssembly'})
  wrapper=job/'ValueRuntime.lean';output=job/'observed.json';report=job/'typed-import.json'
  text=(FIXTURE/'ValueAdapter.lean').read_text()+f'\nopen Lean Solidity.Frontend\nsolc_import {json.dumps(str(ast))} hash {fnv(ast.read_bytes())} as ValueEntry testing entrypoints\n'
  text+=f'#eval IO.FS.writeFile {json.dumps(str(report))} (toJson (ValueEntry.report.map fun (r : ImportRow) => Json.mkObj [("rawRepr",toJson (reprStr r)),("sourceId",toJson r.sourceId),("signature",toJson r.sourceSignature),("name",toJson r.name),("status",toJson r.status.toStr),("admissionChecked",toJson r.admissionChecked),("payable",toJson r.payable)])).pretty\n'
  text+=f'#eval do\n  let data ← match BaselineValue.run ValueEntry ValueEntry.report with\n    | .ok data => pure data\n    | .error reason => throw (IO.userError reason)\n  IO.FS.writeFile {json.dumps(str(output))} data.pretty\n'
  text+='#print axioms Solidity.Lifetime.System.run_ok\n#check Solidity.Lifetime.Step.rollback\n#print axioms Solidity.Lifetime.World.enter_zero\n'
  wrapper.write_text(text);call('typed-value-runtime',['lean','-j1','--tstack=131072',str(wrapper)],job)
  negInput=ROOT/f'tests/upstream/baseline-20261028/native-cache/runs/NativePositive/{mode}/negative-jobs.json';negOutput=job/'false-output.json';negFile=job/'FalseOutput.lean';negFile.write_text(f'import Solidity.Tools.Upstream\n#upstream_batch {json.dumps(str(negInput))} to {json.dumps(str(negOutput))}\n');call('unchanged-false-output',['lean','-j1','--tstack=131072',str(negFile)],job)
 assert all(sha(Path(p))==v for p,v in before['snapshots'].items())
 (BASE/(attempt+'-after.json')).write_text(json.dumps(dict(allSharedArtifactsUnchanged=True,cgroupPeakBytes=int(Path('/sys/fs/cgroup/memory.peak').read_text()),memoryMaxBytes=int(Path('/sys/fs/cgroup/memory.max').read_text()),swapMaxBytes=int(Path('/sys/fs/cgroup/memory.swap.max').read_text()),memoryEvents=Path('/sys/fs/cgroup/memory.events').read_text()),indent=2)+'\n')
if __name__=='__main__':main()
