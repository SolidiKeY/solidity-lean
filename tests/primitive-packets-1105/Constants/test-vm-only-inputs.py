#!/usr/bin/env python3
"""Exercise each missing-input boundary without removing or changing VM data."""
import contextlib,io,pathlib,runpy,sys,tempfile,shutil,subprocess
from unittest.mock import patch
F=pathlib.Path(__file__).resolve().parent
count=0
for script in ['registration-plan.py','validate-fresh.py','h44-storage-check.py']:
 ns=runpy.run_path(str(F/script))
 required=ns['required_inputs']()
 for absent in required:
  output=io.StringIO()
  with patch.object(pathlib.Path,'is_file',lambda p:p!=absent),patch.object(sys,'argv',[script]),contextlib.redirect_stdout(output):
   try:ns['main']()
   except SystemExit as error:message=str(error)
   else:raise AssertionError('missing evidence accepted')
  text=message
  assert 'FAIL:' in text and 'missing' in text and str(absent) in text,text
  assert 'PASS:' not in text,text
  count+=1
with tempfile.TemporaryDirectory(prefix='numeric-portable-tree-') as td:
 root=pathlib.Path(td);source=F.parents[2]
 paths=['scripts/check-sol-numeric-literals.py','tests/sol-numeric-literals/packetlib.py','tests/primitive-packets-1105/Constants/h44-bulk-manifest.json']+['tests/primitive-packets-1105/Constants/'+s for s in ['registration-plan.py','validate-fresh.py','h44-storage-check.py']]
 for relative in paths:
  target=root/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source/relative,target)
 for script in paths[3:]:
  result=subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,text=True)
  assert result.returncode!=0 and 'FAIL:' in result.stderr and 'PASS:' not in result.stdout,(script,result.stdout,result.stderr)
print('PASS: 3 actual standalone no-bulk script runs and '+str(count)+' individual missing-input cases fail closed without claiming validation; no VM data mutated')
