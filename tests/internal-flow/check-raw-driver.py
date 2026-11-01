#!/usr/bin/env python3
"""No-Lean driver coverage/fail-fast controls; never a raw-source gate."""
import json,os,subprocess,tempfile,shutil
from pathlib import Path
repo=Path(__file__).resolve().parents[2]
expected=[str(p.relative_to(repo)) for p in sorted((repo/'Solidity/Backend/InternalFlow').glob('*.lean'))]
expected+=['tests/internal-flow/AxiomReports.lean','tests/internal-flow/PublishedMemoryCalls.lean','tests/internal-flow/MutatingMemoryCalls.lean','tests/internal-flow/TupleMemoryCalls.lean']
with tempfile.TemporaryDirectory(prefix='v12-raw-driver-control-') as tmp:
 root=Path(tmp);binary=root/'lake'
 binary.write_text("#!/usr/bin/env python3\nimport json,os,sys\nassert sys.argv[1:3]==['env','node']\nwith open(os.environ['V12_RAW_CONTROL_LOG']+'.lake','a') as f: f.write(json.dumps(sys.argv[1:])+chr(10))\nif os.environ.get('V12_RAW_CONTROL_SETUP_FAIL'): sys.exit(9)\nif os.environ.get('V12_RAW_CONTROL_NO_LEAN'): os.environ['PATH']=os.environ['V12_RAW_CONTROL_NO_LEAN']\nos.execv(os.environ['V12_RAW_NODE'],sys.argv[2:])\n")
 lean=root/'lean'
 lean.write_text("#!/usr/bin/env python3\nimport json,os,sys\nwith open(os.environ['V12_RAW_CONTROL_LOG'],'a') as f: f.write(json.dumps({'args':sys.argv[1:],'pid':os.getpid(),'marker':os.environ.get('V12_RAW_MARKER')})+chr(10))\nos.write(1,b'OUT\\n');os.write(2,b'ERR\\n')\nif os.environ.get('V12_RAW_CONTROL_SIGNAL'): os.kill(os.getpid(),15)\nif os.environ.get('V12_RAW_CONTROL_MUTATE'): open(os.environ['V12_RAW_CONTROL_MUTATE'],'w').write('')\nsys.exit(7 if sys.argv[-1]==os.environ.get('V12_RAW_CONTROL_FAIL') else 0)\n")
 lean.chmod(0o755)
 binary.chmod(0o755);rows=[]
 for index in [None,*range(len(expected))]:
  out=root/str(index);out.mkdir();log=out/'calls.jsonl';env=dict(os.environ,PATH=str(root)+os.pathsep+os.environ['PATH'],V12_RAW_CONTROL_LOG=str(log),V12_RAW_NODE=shutil.which('node'),V12_RAW_MARKER='inherited-lake-environment',V12_RAW_CONTROL_FAIL='' if index is None else expected[index])
  result=subprocess.run(['bash','tests/internal-flow/check-files.sh',str(out)],cwd=repo,env=env,capture_output=True,text=True)
  assert log.exists(), (result.returncode,result.stdout,result.stderr)
  records=[json.loads(line) for line in log.read_text().splitlines()]
  calls=[r['args'] for r in records]
  assert all(r['marker']=='inherited-lake-environment' for r in records)
  assert len({r['pid'] for r in records})==len(records)
  setups=Path(str(log)+'.lake').read_text().splitlines()
  assert len(setups)==1
  wanted=expected if index is None else expected[:index+1]
  assert [call[-1] for call in calls]==wanted
  for file in wanted:
   assert (out/('final-'+Path(file).stem+'-diagnostics.log')).read_bytes()==b'OUT\nERR\n'
  assert all(call[:-1]==['-j1','--tstack=131072'] for call in calls)
  assert result.returncode==(0 if index is None else 7)
  rows.append({'stop_index':index,'exit_code':result.returncode,'actual_calls':len(calls)})
 out=root/'setup-failure';out.mkdir();log=out/'calls.jsonl'
 env=dict(os.environ,PATH=str(root)+os.pathsep+os.environ['PATH'],V12_RAW_CONTROL_LOG=str(log),V12_RAW_NODE=shutil.which('node'),V12_RAW_MARKER='inherited-lake-environment',V12_RAW_CONTROL_SETUP_FAIL='1')
 result=subprocess.run(['bash','tests/internal-flow/check-files.sh',str(out)],cwd=repo,env=env,capture_output=True,text=True)
 assert result.returncode==9 and not log.exists()
 # Signal and missing-executable controls must stop before a later source.
 for case,extra,code in [('signal',{'V12_RAW_CONTROL_SIGNAL':'1'},143),
                         ('spawn',{'V12_RAW_CONTROL_NO_LEAN':str(root/'empty')},1)]:
  (root/'empty').mkdir(exist_ok=True)
  out=root/case;out.mkdir();log=out/'calls.jsonl'
  env=dict(os.environ,PATH=str(root)+os.pathsep+os.environ['PATH'],V12_RAW_CONTROL_LOG=str(log),V12_RAW_NODE=shutil.which('node'),**extra)
  result=subprocess.run(['bash','tests/internal-flow/check-files.sh',str(out)],cwd=repo,env=env,capture_output=True,text=True)
  assert result.returncode==code,(case,result.returncode,result.stderr)
  assert len(log.read_text().splitlines())==(1 if case=='signal' else 0) if log.exists() else case=='spawn'
  rows.append({'case':case,'exit_code':result.returncode})
 # Test target-membership mutation only in a private mock tree, never this checkout.
 tree=root/'tree'
 for file in expected:
  p=tree/file;p.parent.mkdir(parents=True,exist_ok=True);p.write_text('')
 out=root/'membership';out.mkdir();log=out/'calls.jsonl'
 added=tree/'Solidity/Backend/InternalFlow/NewMembership.lean'
 env=dict(os.environ,PATH=str(root)+os.pathsep+os.environ['PATH'],V12_RAW_CONTROL_LOG=str(log),V12_RAW_NODE=shutil.which('node'),V12_RAW_CONTROL_MUTATE=str(added))
 result=subprocess.run(['node',str(repo/'tests/internal-flow/raw-source-driver.mjs'),str(out)],cwd=tree,env=env,capture_output=True,text=True)
 assert result.returncode==1 and 'changed during check' in result.stderr
 assert json.loads((out/'raw-source-batch.json').read_text())['unchanged'] is False
 rows.append({'case':'target-membership-change','exit_code':result.returncode})
 # Empty source enumeration must not silently narrow the original workload.
 empty=root/'empty-tree';(empty/'Solidity/Backend/InternalFlow').mkdir(parents=True)
 out=root/'empty-source';out.mkdir();log=out/'calls.jsonl'
 env=dict(os.environ,PATH=str(root)+os.pathsep+os.environ['PATH'],V12_RAW_CONTROL_LOG=str(log))
 result=subprocess.run(['node',str(repo/'tests/internal-flow/raw-source-driver.mjs'),str(out)],cwd=empty,env=env,capture_output=True,text=True)
 assert result.returncode==2 and not log.exists()
 rows.append({'case':'empty-source-list','exit_code':result.returncode})
 print(json.dumps({'status':'pass','no_Lean_run':True,'not_source_validation':True,'exact_targets':expected,'controls':rows},indent=2))
