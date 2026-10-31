#!/usr/bin/env python3
"""Adversarial evidence checks; never edits Lean sources or deletes fixtures.
These are external validation tests, separate from kernel negative controls.
"""
import copy, json, subprocess, sys, tempfile
from pathlib import Path
root = Path(__file__).resolve().parent.parent
original = json.loads(Path(sys.argv[1]).read_text())
# Never overwrite prior checkpoint fixtures or remove this persistent directory.
fixtures = Path(tempfile.mkdtemp(prefix='v08-evidence-controls-', dir='/workspace/v08-world-lowering-evidence'))
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
handler='Solidity/Lowering/V08/HandlerControls.lean'
assert handler in original['source_sha256'], 'handler source absent from current evidence'
result=copy.deepcopy(original);result['source_sha256'][handler]='0'*64;check('changed-handler-source',result,False)
result=copy.deepcopy(original);result['source_sha256'].pop(handler);check('missing-handler-source',result,False)
library_handler='Solidity/Lowering/V08/LibraryHandlerControls.lean'
assert library_handler in original['source_sha256'], 'library-handler source absent from current evidence'
result=copy.deepcopy(original);result['source_sha256'][library_handler]='0'*64;check('changed-library-handler-source',result,False)
result=copy.deepcopy(original);result['source_sha256'].pop(library_handler);check('missing-library-handler-source',result,False)
print('PASS: current evidence accepted; thirteen corrupted/guarded evidence controls rejected; fixtures='+str(fixtures))

success='Solidity/Lowering/V08/CreationSuccessControls.lean'
assert success in original['source_sha256']
result=copy.deepcopy(original);result['source_sha256'][success]='0'*64;check('changed-success-creation-source',result,False)
result=copy.deepcopy(original);result['source_sha256'].pop(success);check('missing-success-creation-source',result,False)
print('PASS: fifteen corruption controls rejected after accepting current positive evidence')

for module in ['TransactionPrefixes','PrefixControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: nineteen corruption controls rejected after positive current evidence')

for module in ['SourceKeccak','SourceKeccakControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: actual Source Keccak evidence corruption controls rejected')

for module in ['SourceEmit','SourceEmitControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: source emit evidence corruption controls rejected')

for module in ['SourceCallable','SourceCallableControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: source callable evidence corruption controls rejected')

for module in ['SourceDispatch','SourceDispatchControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: source dispatch evidence corruption controls rejected')

for module in ['SourceCustomErrors','SourceCustomErrorControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: source custom-error evidence corruption controls rejected')
