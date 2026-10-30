#!/usr/bin/env python3
"""Adversarial evidence checks; never edits Lean sources or deletes fixtures.
These are external validation tests, separate from kernel negative controls.
"""
import copy, json, subprocess, sys
from pathlib import Path
root = Path(__file__).resolve().parent.parent
original = json.loads(Path(sys.argv[1]).read_text())
fixtures = Path('/workspace/v08-world-lowering-evidence/control-negative-cases')
fixtures.mkdir(exist_ok=True)
checker = root/'scripts/v08-check.py'
def check(name, result, expected):
 path=fixtures/(name+'.json');path.write_text(json.dumps(result,indent=2)+'\n')
 proc=subprocess.run([sys.executable,str(checker),str(path)],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (fixtures/(name+'.log')).write_text('exit='+str(proc.returncode)+'\n'+proc.stdout)
 assert (proc.returncode==0)==expected, (name,proc.stdout)
check('valid-current-evidence',copy.deepcopy(original),True)
for name,key,value in [('guard-stop','resource_or_time_guard_stopped',True),('zero-samples','samples',0),('changed-during-build','source_unchanged',False),('changed-log','log_sha256','0'*64)]:
 result=copy.deepcopy(original);result[key]=value;check(name,result,False)
result=copy.deepcopy(original);key=next(iter(result['source_sha256']));result['source_sha256'][key]='0'*64;check('changed-source',result,False)
result=copy.deepcopy(original);result['source_sha256'].pop(next(iter(result['source_sha256'])));check('missing-source',result,False)
result=copy.deepcopy(original);result['runtime_configuration']['sha256']='0'*64;check('changed-config',result,False)
result=copy.deepcopy(original);result['tool_versions'][0]='wrong toolchain';check('wrong-toolchain',result,False)
result=copy.deepcopy(original);result['container_cleanup_verified']=False;check('unconfirmed-container-stop',result,False)
print('PASS: current evidence accepted; nine corrupted/guarded evidence controls rejected')
