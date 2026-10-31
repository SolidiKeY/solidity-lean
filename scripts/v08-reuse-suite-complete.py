#!/usr/bin/env python3
"""Reuse one exact stopped published-tree runtime; no container allocation.
All original bounded-runner guards, time/proof budgets and cache settings remain.
"""
import ast, hashlib, json, os, runpy, subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parent.parent
decision=True
assert sys.argv[1:]==[]
if decision: sys.argv=[sys.argv[0],'Solidity.KeySort','SolkeyTestSuite']
seed=Path('/workspace/v08-world-lowering-evidence/'+('v08-gate-119252-8018ce25.json' if decision else 'v08-gate-42879-c1a2dd7c.json'))
previous=json.loads(seed.read_text());seed_hash=hashlib.sha256(seed.read_bytes()).hexdigest()
assert previous['repository']==str(root) and previous['source_unchanged']
assert previous['reused_from']=='/workspace/v08-world-lowering-evidence/v08-gate-98977-30eb36e8.json'
assert previous['configured_command']==json.loads(Path(previous['reused_from']).read_text())['command']
previous['command']=previous['configured_command']
assert previous['container_cleanup_verified']
assert decision or not previous['resource_or_time_guard_stopped']
if decision: assert previous['exit']==125 and previous['resource_or_time_guard_stopped']
assert previous['modules'][-1]==('SolkeyTestSuite' if decision else 'Solidity.Lowering.V08.SourceFailureControls')
assert hashlib.sha256(Path(previous['log']).read_bytes()).hexdigest()==previous['log_sha256']
# Reuse the previously reviewed strict inspection implementation without executing
# that driver or its old source/config/cache policy.
tree=ast.parse((root/'scripts/v08-reuse-prefix.py').read_text())
function=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='inspect_reuse')
fmt=ast.literal_eval(next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='fmt' for t in n.targets)).value)
exec(compile(ast.Module(body=[function],type_ignores=[]),'<strict-runtime-inspection>','exec'))
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
assert ordered==previous['modules'] and not full and not baseline and not fresh_sort and not native_modules
assert configuration_before==previous['runtime_configuration']['sha256']
assert cmd[-1]==previous['command'][-1]
if decision:
 for module in ordered:
  path=str(graph.source(module).relative_to(root))
  assert digest_if_file(root/path)==previous['source_sha256'][path]
 completed={}
 cutoff=Path(previous['log']).stat().st_mtime_ns
 boundary=ordered.index('Solidity.TestSuite.Derived21')
 assert ordered[boundary-1]=='Solidity.TestSuite.Derived20'
 assert not (root/'.lake/build/lib/lean/Solidity/TestSuite/Derived21.olean').exists()
 for module in ordered[:boundary]:
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
 warm=root/'.lake/build/lib/lean/Solidity/TestSuite/Derived20.olean'
 assert warm.is_file() and 'Built Solidity.TestSuite.Derived20 (149s)' in Path(previous['log']).read_text()
 (evidence/(name+'-warm-repair.json')).write_text(json.dumps(dict(
  cause='Previous Suite attempt completed Derived10..20 including Derived17 144s and Derived20 149s; same targets/600s guard, all imported completed outputs certified',
  cold_gate=str(seed),warm_output=str(warm),sha256=digest_if_file(warm),bytes=warm.stat().st_size,completed_prefix=completed,cutoff_ns=cutoff),indent=2)+'\\n')
inspection=inspect_reuse(docker,env)
(evidence/(name+'-reuse-before.json')).write_text(json.dumps(inspection,indent=2)+'\\n')
cmd=docker+['start','--attach',previous['container']]
''')
change('container=name)', "container=previous['container'], configured_command=previous['command'], reused_from=str(seed))")
ast.parse(source)
exec(compile(source,str(root/'scripts/v08-bounded.py'),'exec'),dict(
 __name__='__main__',__file__=str(root/'scripts/v08-bounded.py'),previous=previous,
 seed=seed,seed_hash=seed_hash,inspect_reuse=inspect_reuse,decision=decision))
