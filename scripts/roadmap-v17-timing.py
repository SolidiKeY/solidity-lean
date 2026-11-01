#!/usr/bin/env python3
"""Consumer for the unchanged published24-module fresh timing contract."""
import hashlib,importlib.util,json,math,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
MODULES=['Solidity.Calculus.MemoryLoopReplay']+['Solidity.TestSuite.MemoryLoopReplay.'+kind+f'{i:02}' for kind in ['Discover','Assemble'] for i in range(10)]+['Solidity.TestSuite.Derived17MemoryLoop','Solidity.TestSuite.MemoryLoopReplay.Refusals','Solidity.TestSuite.Derived17']
def load_loop():
 s=importlib.util.spec_from_file_location('timing_loop',ROOT/'scripts/roadmap-v17-loops.py');l=importlib.util.module_from_spec(s);s.loader.exec_module(l);return l

def prerequisites():
 return {'expectedModules':MODULES,'missingSetups':[m for m in MODULES if not (ROOT/'.lake/build/ir'/(m.replace('.','/')+'.setup.json')).is_file()],'releaseClosed':False}

def validate_shape(result,hash_source):
 def seconds(x):return type(x) in (int,float) and math.isfinite(x) and x>=0
 if result.get('kind')!='fresh-original-Derived17-workload' or type(result.get('exit_code')) is not int or result['exit_code']!=0 or type(result.get('budgetSeconds')) is not int or result['budgetSeconds']!=300 or not seconds(result.get('seconds')) or result['seconds']>300:raise ValueError('failed/incomplete/over-budget original cumulative workload')
 if result.get('expectedModules')!=MODULES or [x.get('module') for x in result.get('checks',[])]!=MODULES:raise ValueError('missing/reordered/duplicate workload members')
 total=0
 for row in result['checks']:
  if row.get('fresh') is not True or type(row.get('exit_code')) is not int or row['exit_code']!=0 or not seconds(row.get('seconds')) or row.get('sourceSha256')!=hash_source(row['module']):raise ValueError('cached/failed/stale original member')
  total+=row['seconds']
 if total>300 or total>result['seconds']+0.1:raise ValueError('cumulative member budget exceeded/inconsistent')
 return {'members':24,'sumMemberSeconds':total,'cumulativeSeconds':result['seconds'],'semanticPremisesDischarged':False,'releaseClosed':False}

def verify(record,directory,current,producer,producer_directory):
 l=load_loop();m=l.creation().load_memory();k=m.load_kernel();m.verify_stage(k,record,directory,current,producer,producer_directory,None,'warm-derived17-prerequisites','fresh-derived17')
 for name in ['scripts/check-memory-loop-timing.py','scripts/check-memory-loop-timing.mjs']:
  if (ROOT/name).read_bytes()!=subprocess.check_output(['git','show',l.PUBLICATION+':'+name],cwd=ROOT):raise ValueError('changed published timing driver/validator')
 manifest=k.p.validate_timing_outputs(record,directory)
 result=k.e.loads(k.p.read_bound(directory,manifest['workload']['path'],manifest['workload']['sha256']));summary=validate_shape(result,lambda mod:hashlib.sha256((ROOT/(mod.replace('.','/')+'.lean')).read_bytes()).hexdigest())
 group=directory/'fresh-group';artifacts={}
 raw=k.p.read_bound(directory,record['log'],record['logSha256']).decode().splitlines()
 expected_lines=[str(row['module'])+' '+str(row['exit_code'])+' '+str(row['seconds']) for row in result['checks']]
 if raw!=expected_lines:raise ValueError('raw driver rows disagree with workload report')
 for row in result['checks']:
  mod=row['module'];source=ROOT/(mod.replace('.','/')+'.lean');out=group/(mod+'.olean');log=group/(mod+'.log');setup=group/(mod+'.setup.json')
  expected=['lean','-j1','--tstack=32768','--setup',str(setup),str(source),'-o',str(out),'-c',str(group/(mod+'.c'))]
  if row.get('command')!=expected or row.get('source')!=str(source) or row.get('output')!=str(out) or row.get('log')!=str(log):raise ValueError('wrong original driver argv/artifacts')
  if (group/(mod+'.source.lean')).read_bytes()!=source.read_bytes() or out.stat().st_size==0:raise ValueError('missing/stale fresh source/output')
  for path in [out,log,setup,group/(mod+'.source.lean'),group/(mod+'.c')]:
   rel=str(path.relative_to(group));sha=manifest['fresh']['files'].get(rel)
   if sha is None:raise ValueError('unmatched producer artifact')
   k.p.read_bound(group,rel,sha);artifacts[str(path.relative_to(directory))]=sha
 # Published consumer is reused read-only, with exact current source hashes.
 check=subprocess.run(['node',str(ROOT/'scripts/check-memory-loop-timing.mjs'),str(directory/'workload.json')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if check.returncode:raise ValueError('published cumulative validator rejected: '+check.stdout.decode())
 return {'summary':summary,'artifacts':artifacts,'producerOutputManifest':record['timingOutputs'],'publishedValidatorOutput':check.stdout.decode(),'sourceSnapshot':current,'pythonInputs':record['pythonInputsBefore'],'semanticPremisesDischarged':False,'releaseClosed':False,'boundary':'Fresh original24-member workload only, not whole suite/corpus/compiler/cache or release closure.'}

if __name__=='__main__':
 import argparse,fcntl
 from types import SimpleNamespace
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--producer',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--verified',type=Path,required=True);a=p.parse_args()
 try:
  l=load_loop();k=l.creation().load_memory().load_kernel()
  with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a+') as lock:
   fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
   pre=prerequisites()
   if pre['missingSetups']:raise ValueError('missing published workload setups: '+','.join(pre['missingSetups']))
   current=k.e.snapshot(ROOT);producer=k.e.load(a.producer)
   if k.p.validate(producer,a.producer.parent,current,'warm-derived17-prerequisites',live_outputs=True) is not True:raise ValueError('failed/missing current prerequisite gate')
   if k.p.collect(SimpleNamespace(gate='fresh-derived17',out=a.out))!=0:raise ValueError('fresh cumulative workload failed')
   result=verify(k.e.load(a.out/'provenance.json'),a.out,k.e.snapshot(ROOT),producer,a.producer.parent);a.verified.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['summary']))
 except (ValueError,KeyError,TypeError,OSError) as e:print(json.dumps({'error':str(e),'releaseClosed':False}));raise SystemExit(2)
