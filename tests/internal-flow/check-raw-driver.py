#!/usr/bin/env python3
"""No-Lean driver coverage/fail-fast controls; never a raw-source gate."""
import json,os,subprocess,tempfile
from pathlib import Path
repo=Path(__file__).resolve().parents[2]
expected=[str(p.relative_to(repo)) for p in sorted((repo/'Solidity/Backend/InternalFlow').glob('*.lean'))]
expected+=['tests/internal-flow/AxiomReports.lean','tests/internal-flow/PublishedMemoryCalls.lean','tests/internal-flow/MutatingMemoryCalls.lean','tests/internal-flow/TupleMemoryCalls.lean']
with tempfile.TemporaryDirectory(prefix='v12-raw-driver-control-') as tmp:
 root=Path(tmp);binary=root/'lake'
 binary.write_text("#!/usr/bin/env python3\nimport json,os,sys\nwith open(os.environ['V12_RAW_CONTROL_LOG'],'a') as f:\n    f.write(json.dumps(sys.argv[1:])+chr(10))\nsys.exit(7 if sys.argv[-1]==os.environ.get('V12_RAW_CONTROL_FAIL') else 0)\n")
 binary.chmod(0o755);rows=[]
 for index in [None,0,len(expected)//2,len(expected)-1]:
  out=root/str(index);out.mkdir();log=out/'calls.jsonl';env=dict(os.environ,PATH=str(root)+os.pathsep+os.environ['PATH'],V12_RAW_CONTROL_LOG=str(log),V12_RAW_CONTROL_FAIL='' if index is None else expected[index])
  result=subprocess.run(['bash','tests/internal-flow/check-files.sh',str(out)],cwd=repo,env=env,capture_output=True,text=True)
  assert log.exists(), (result.returncode,result.stdout,result.stderr)
  calls=[json.loads(line) for line in log.read_text().splitlines()]
  wanted=expected if index is None else expected[:index+1]
  assert [call[-1] for call in calls]==wanted
  assert all(call[:-1]==['env','lean','-j1','--tstack=131072'] for call in calls)
  assert result.returncode==(0 if index is None else 7)
  rows.append({'stop_index':index,'exit_code':result.returncode,'actual_calls':len(calls)})
 print(json.dumps({'status':'pass','no_Lean_run':True,'not_source_validation':True,'exact_targets':expected,'controls':rows},indent=2))
