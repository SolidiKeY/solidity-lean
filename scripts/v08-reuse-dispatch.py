#!/usr/bin/env python3
"""Reuse one exact stopped published-tree runtime; no container allocation.
All original bounded-runner guards, time/proof budgets and cache settings remain.
"""
import ast, hashlib, json, os, runpy, subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parent.parent
decision=False
assert sys.argv[1:]==[]
sys.argv=[sys.argv[0],'Solidity.KeySort','Solidity.Lowering.V08.PrefixControls']
if decision: sys.argv=[sys.argv[0],'Solidity.KeySort','Solidity.Examples.Decision']
seed=Path('/workspace/v08-world-lowering-evidence/'+('v08-gate-22265-74624f2d.json' if decision else 'v08-gate-65693-05d6dedc.json'))
previous=json.loads(seed.read_text());seed_hash=hashlib.sha256(seed.read_bytes()).hexdigest()
assert previous['repository']==str(root) and previous['source_unchanged']
assert previous['container_cleanup_verified'] and previous['exit']==0
assert decision or not previous['resource_or_time_guard_stopped']
if decision: assert previous['exit']==125 and previous['resource_or_time_guard_stopped']
assert previous['modules'][-1]==('Solidity.Examples.Decision' if decision else 'Solidity.Lowering.V08.PrefixControls')
assert hashlib.sha256(Path(previous['log']).read_bytes()).hexdigest()==previous['log_sha256']
# Reuse the previously reviewed strict inspection implementation without executing
# that driver or its old source/config/cache policy.
tree=ast.parse((root/'scripts/v08-reuse-prefix.py').read_text())
function=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='inspect_reuse')
fmt=ast.literal_eval(next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='fmt' for t in n.targets)).value)
exec(compile(ast.Module(body=[function],type_ignores=[]),'<strict-runtime-inspection>','exec'))
def validate_extension(previous,ordered,imports,audit):
 assert previous['exit']==0 and not previous['resource_or_time_guard_stopped']
 old=set(previous['modules'])
 core='Solidity.Lowering.V08.SourceDispatch'
 controls=core+'Controls'
 prior={'Solidity.Lowering.V08.SourceKeccak','Solidity.Lowering.V08.SourceKeccakControls','Solidity.Lowering.V08.SourceEmit','Solidity.Lowering.V08.SourceEmitControls','Solidity.Lowering.V08.SourceCallable','Solidity.Lowering.V08.SourceCallableControls'}
 assert old <= set(ordered) and set(ordered)-old==prior | {core,controls}
 assert set(imports(core)) <= old | prior
 assert imports(controls)[0]==core
 assert set(imports(controls)) <= old | {core}
 prefix=('import '+controls+'\nimport Solidity.Lowering.V08.SourceCallableControls\nimport Solidity.Lowering.V08.SourceEmitControls\nimport Solidity.Lowering.V08.SourceKeccakControls\n').encode()
 assert audit.startswith(prefix)
 assert hashlib.sha256(audit[len(prefix):]).hexdigest()==previous['source_sha256']['Solidity/Lowering/V08/Audit.lean']

def validate_prior(certificate,actual,config,versions,log_sha):
 assert certificate['exit']==0 and certificate['source_unchanged']
 assert certificate['container_cleanup_verified'] and not certificate['resource_or_time_guard_stopped']
 assert certificate['runtime_configuration']['unchanged']
 assert certificate['runtime_configuration']['sha256']==config
 assert certificate['tool_versions']==versions and certificate['log_sha256']==log_sha
 for module in ['SourceKeccak','SourceKeccakControls','SourceEmit','SourceEmitControls','SourceCallable','SourceCallableControls']:
  path='Solidity/Lowering/V08/'+module+'.lean'
  assert path in certificate['source_sha256'] and path in actual
  assert actual[path]==certificate['source_sha256'][path]

saved=sys.argv
sys.argv=[str(root/'scripts/v08-no-artifact-cache.py'),'--self-test']
ns=runpy.run_path(str(root/'scripts/v08-no-artifact-cache.py'));sys.argv=saved
source=ns['source']
def change(old,new,count=1):
 global source
 assert source.count(old)==count,(old,source.count(old));source=source.replace(old,new)
line="name = 'v08-gate-' + str(os.getpid()) + '-' + run_token[:8]"
change(line,line+"\nrun_token = previous['run_token']")
change("docker + ['top', name,","docker + ['top', previous['container'],")
change('cleanup.ensure_stopped(docker, name, run_token, log, env=env)',
 "cleanup.ensure_stopped(docker, previous['container'], run_token, log, env=env)",2)
change('cmd[-1] = script', '''cmd[-1] = script
assert not full and not baseline and not fresh_sort and not native_modules
validate_extension(previous,ordered,graph.imports,(root/'Solidity/Lowering/V08/Audit.lean').read_bytes())
certificate=json.loads((evidence/'v08-gate-35093-a7d079b2.json').read_text())
validate_prior(certificate,{path:digest_if_file(root/path) for path in
 ['Solidity/Lowering/V08/SourceKeccak.lean','Solidity/Lowering/V08/SourceKeccakControls.lean','Solidity/Lowering/V08/SourceEmit.lean','Solidity/Lowering/V08/SourceEmitControls.lean','Solidity/Lowering/V08/SourceCallable.lean','Solidity/Lowering/V08/SourceCallableControls.lean']},
 configuration_before,previous['tool_versions'],digest_if_file(Path(certificate['log'])))
for module in previous['modules']:
 path=str(graph.source(module).relative_to(root))
 if module!='Solidity.Lowering.V08.Audit': assert digest_if_file(root/path)==previous['source_sha256'][path]
assert configuration_before==previous['runtime_configuration']['sha256']
# Every original explicit target is retained; Audit now depends on the two
# new modules, whose only cold dependency chain is linear.
cmd[-1]=previous['command'][-1]
if decision:
 for module in ordered:
  path=str(graph.source(module).relative_to(root))
  assert digest_if_file(root/path)==previous['source_sha256'][path]
 completed={}
 cutoff=Path(previous['log']).stat().st_mtime_ns
 assert ordered[-2:] == ['Solidity.Examples.DecisionHashes','Solidity.Examples.Decision']
 for module in ordered[:-2]:
  rel=Path(module.replace('.','/'))
  lib=root/'.lake/build/lib/lean'/rel
  ir=root/'.lake/build/ir'/rel
  files=[lib.with_suffix(ext) for ext in ['.olean','.olean.hash','.ilean','.ilean.hash','.trace']]
  files += [ir.with_suffix(ext) for ext in ['.c','.c.hash','.setup.json']]
  trace=json.loads(lib.with_suffix('.trace').read_text())
  assert trace['outputs']['o']==[lib.with_suffix('.olean.hash').read_text().strip()]
  assert trace['outputs']['i']==lib.with_suffix('.ilean.hash').read_text().strip()
  assert trace['outputs']['c']==ir.with_suffix('.c.hash').read_text().strip()
  metadata={}
  for artifact in files:
   stat=artifact.stat()
   assert stat.st_ctime_ns <= cutoff, ('artifact changed after cold prefix',artifact)
   metadata[str(artifact)]=dict(bytes=stat.st_size,ctime_ns=stat.st_ctime_ns,sha256=digest_if_file(artifact))
  completed[module]=dict(source_sha256=previous['source_sha256'][str(graph.source(module).relative_to(root))],artifacts=metadata)
 warm=root/'.lake/build/lib/lean/Solidity/Examples/Tactics/Hashing.olean'
 assert warm.is_file() and 'Built Solidity.Examples.Tactics.Hashing (128s)' in Path(previous['log']).read_text()
 (evidence/(name+'-warm-repair.json')).write_text(json.dumps(dict(
  cause='Cold published dependency rebuild; completed Hashing alone consumed 128s before DecisionHashes; same 600s guard now reuses source-bound completed outputs',
  cold_gate=str(seed),warm_output=str(warm),sha256=digest_if_file(warm),bytes=warm.stat().st_size,completed_prefix=completed,cutoff_ns=cutoff),indent=2)+'\\n')
(evidence/(name+'-dispatch-binding.json')).write_text(json.dumps(dict(
 wrapper_sha256=digest_if_file(root/'scripts/v08-reuse-dispatch.py'),
 generated_sha256=hashlib.sha256(source.encode()).hexdigest(),
 current_closure=ordered,original_explicit_targets=previous['modules'],seed_sha256=seed_hash),indent=2)+'\\n')
inspection=inspect_reuse(docker,env)
(evidence/(name+'-reuse-before.json')).write_text(json.dumps(inspection,indent=2)+'\\n')
cmd=docker+['start','--attach',previous['container']]
''')
change('container=name)', "container=previous['container'], configured_command=previous['command'], reused_from=str(seed))")
ast.parse(source)
exec(compile(source,str(root/'scripts/v08-bounded.py'),'exec'),dict(
 __name__='__main__',__file__=str(root/'scripts/v08-bounded.py'),previous=previous,
 validate_prior=validate_prior,validate_extension=validate_extension,source=source,seed=seed,seed_hash=seed_hash,inspect_reuse=inspect_reuse,decision=decision))
