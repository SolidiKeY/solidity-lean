#!/usr/bin/env python3
"""Inspect-only source-extension/guard controls: no Docker start or Lean."""
import ast,copy,hashlib,json,sys,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent.parent
p=root/'scripts/v08-reuse-callable.py';tree=ast.parse(p.read_text())
function=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='validate_extension')
ns={'hashlib':hashlib};exec(compile(ast.Module(body=[function],type_ignores=[]),'extension-test','exec'),ns)
check=ns['validate_extension']
previous=json.loads(Path('/workspace/v08-world-lowering-evidence/v08-gate-65693-05d6dedc.json').read_text())
core='Solidity.Lowering.V08.SourceCallable';controls=core+'Controls'
ordered=previous['modules']+['Solidity.Lowering.V08.SourceKeccak','Solidity.Lowering.V08.SourceKeccakControls','Solidity.Lowering.V08.SourceEmit','Solidity.Lowering.V08.SourceEmitControls',core,controls]
imports={core:['Solidity.Lowering.V08.SourceEmit'],controls:[core,'Solidity.Lowering.V08.SourceEnvironmentControls','Solidity.Lowering.V08.CryptoControls']}
fixture_commit='3c4f9f829649bdee366bcf6a11deecb528a33fd5'
fixture_sha256='de5a0ae3ab1b21dd7ed961ae0804c39667a287b7c1c0cfdf34bbd129bc8aec07'
audit=subprocess.check_output(['git','show',fixture_commit+':Solidity/Lowering/V08/Audit.lean'],cwd=root)
assert hashlib.sha256(audit).hexdigest()==fixture_sha256
fixture_certificate=json.loads(Path('/workspace/v08-world-lowering-evidence/v08-gate-14531-f974b989.json').read_text())
assert fixture_certificate['source_sha256']['Solidity/Lowering/V08/Audit.lean']==fixture_sha256
audit=b'import Solidity.Lowering.V08.SourceCallableControls\n'+audit
current_audit=(root/'Solidity/Lowering/V08/Audit.lean').read_bytes()
if current_audit!=audit:
 try:check(previous,ordered,imports.__getitem__,current_audit)
 except AssertionError:pass
 else:raise AssertionError('callable guard accepted a different current Audit')
check(previous,ordered,imports.__getitem__,audit)
cases=[]
bad=copy.deepcopy(previous);bad['exit']=1;cases.append(('failed-seed',bad,ordered,imports,audit))
bad=copy.deepcopy(previous);bad['resource_or_time_guard_stopped']=True;cases.append(('stopped-seed',bad,ordered,imports,audit))
cases += [('missing-old',previous,ordered[1:],imports,audit),('extra-module',previous,ordered+['Foreign'],imports,audit),('changed-audit',previous,ordered,imports,audit+b' '),('missing-audit-import',previous,ordered,imports,audit.split(b'\n',1)[1])]
for key,values in [(core,[controls]),(controls,['Foreign',core]),(controls,[core,'Foreign'])]:
 bad=copy.deepcopy(imports);bad[key]=values;cases.append(('bad-import-'+key,previous,ordered,bad,audit))
for name,old,modules,deps,content in cases:
 try: check(old,modules,deps.__getitem__,content)
 except AssertionError: pass
 else: raise AssertionError('accepted '+name)
assert isinstance(tree.body[-1],ast.Expr);tree.body.pop()
saved=sys.argv;sys.argv=[str(p)];ns={'__file__':str(p)}
exec(compile(tree,str(p),'exec'),ns);sys.argv=saved
generated=ns['source'];ast.parse(generated)
for guard in ["wall_limit_seconds = 600", "'--memory', '12g'", "'--memory-swap', '12g'", "'-e', 'LAKE_CACHE_DIR=', '-e', 'LAKE_ARTIFACT_CACHE=false'", "cmd=docker+['start','--attach',previous['container']]", "cmd[-1]=previous['command'][-1]", "validate_extension(previous,ordered", "assert configuration_before==previous['runtime_configuration']['sha256']", "if module!='Solidity.Lowering.V08.Audit': assert digest_if_file", "wrapper_sha256=", "current_closure=ordered"]:
 assert guard in generated,guard
print('PASS: SHA-bound prior Audit plus exact callable prefix; current positive; '+str(len(cases))+' corruption controls; exact generated cache/resource/command/source/config guards; no Docker/Lean/start/write')

# Prior checked Keccak modules are read-only inputs to this additive extension.
function=next(x for x in ast.parse(p.read_text()).body if isinstance(x,ast.FunctionDef) and x.name=='validate_prior')
ns={};exec(compile(ast.Module(body=[function],type_ignores=[]),'prior-test','exec'),ns)
check_prior=ns['validate_prior']
cert=json.loads(Path('/workspace/v08-world-lowering-evidence/v08-gate-14531-f974b989.json').read_text())
actual={path:hashlib.sha256((root/path).read_bytes()).hexdigest() for path in ['Solidity/Lowering/V08/SourceKeccak.lean','Solidity/Lowering/V08/SourceKeccakControls.lean','Solidity/Lowering/V08/SourceEmit.lean','Solidity/Lowering/V08/SourceEmitControls.lean']}
config=cert['runtime_configuration']['sha256'];versions=cert['tool_versions'];log_sha=hashlib.sha256(Path(cert['log']).read_bytes()).hexdigest()
check_prior(cert,actual,config,versions,log_sha)
corrupt=[]
for key,value in [('exit',1),('source_unchanged',False),('container_cleanup_verified',False),('resource_or_time_guard_stopped',True),('tool_versions',['wrong']),('log_sha256','0'*64)]:
 bad=copy.deepcopy(cert);bad[key]=value;corrupt.append((key,bad,actual))
for key,value in [('unchanged',False),('sha256','0'*64)]:
 bad=copy.deepcopy(cert);bad['runtime_configuration'][key]=value;corrupt.append((key,bad,actual))
for path in actual:
 bad=copy.deepcopy(cert);bad['source_sha256'].pop(path);corrupt.append(('missing-'+path,bad,actual))
 changed=dict(actual);changed[path]='0'*64;corrupt.append(('changed-'+path,cert,changed))
for name,old,hashes in corrupt:
 try:check_prior(old,hashes,config,versions,log_sha)
 except AssertionError:pass
 else:raise AssertionError('accepted '+name)
assert 'validate_prior(certificate,' in generated
print('PASS: prior certificate/source positive and '+str(len(corrupt))+' corruptions; no starts/builds/writes')
