#!/usr/bin/env python3
"""Inspect-only source-extension/guard controls: no Docker start or Lean."""
import ast,copy,hashlib,json,sys,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent.parent
p=root/'scripts/v08-reuse-keccak.py';tree=ast.parse(p.read_text())
function=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='validate_extension')
ns={'hashlib':hashlib};exec(compile(ast.Module(body=[function],type_ignores=[]),'extension-test','exec'),ns)
check=ns['validate_extension']
previous=json.loads(Path('/workspace/v08-world-lowering-evidence/v08-gate-65693-05d6dedc.json').read_text())
core='Solidity.Lowering.V08.SourceKeccak';controls=core+'Controls'
ordered=previous['modules']+[core,controls]
imports={core:['Solidity.Lowering.V08.SourceEnvironment','Solidity.Lowering.V08.CryptoObservations'],controls:[core,'Solidity.Lowering.V08.SourceEnvironmentControls','Solidity.Lowering.V08.CryptoControls']}
fixture_commit='aa640d21ec9131f35d24d9a523e7f251e9b70f9b'
fixture_sha256='73c54e69dad346b59e1026f9b0b49cf107fdcf77460e0306a1d67c64289fd2ba'
audit=subprocess.check_output(['git','show',fixture_commit+':Solidity/Lowering/V08/Audit.lean'],cwd=root)
assert hashlib.sha256(audit).hexdigest()==fixture_sha256
certificate=json.loads(Path('/workspace/v08-world-lowering-evidence/v08-gate-180303-e740af0b.json').read_text())
assert certificate['source_sha256']['Solidity/Lowering/V08/Audit.lean']==fixture_sha256
current_audit=(root/'Solidity/Lowering/V08/Audit.lean').read_bytes()
assert current_audit!=audit
try:check(previous,ordered,imports.__getitem__,current_audit)
except AssertionError:pass
else:raise AssertionError('historical guard accepted extended current Audit')
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
print('PASS: committed SHA-bound positive fixture; extended current Audit rejected; '+str(len(cases))+' corruption controls; exact generated cache/resource/command/source/config guards; no Docker/Lean/start/write')
