#!/usr/bin/env python3
"""Inspect-only corruption tests; never starts Docker or executes the driver."""
import ast, copy, hashlib, json, os, types
from pathlib import Path
root=Path(__file__).resolve().parent.parent
tree=ast.parse((root/'scripts/v08-reuse-prefix.py').read_text())
function=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='inspect_reuse')
fmt_node=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='fmt' for t in n.targets))
fmt=ast.literal_eval(fmt_node.value)
seed=Path('/workspace/v08-world-lowering-evidence/v08-gate-42879-c1a2dd7c.json')
previous=json.loads(seed.read_text())
record=max((p for p in seed.parent.glob('v08-gate-*-reuse-before.json') if json.loads(p.read_text())['token']==previous['run_token']),key=lambda p:p.stat().st_mtime)
baseline=json.loads(record.read_text())
current=[baseline]
calls=[]
def fake(args,**kwargs):
 assert kwargs['env']=={'SAFE':'1'} and 'inspect' in args and 'start' not in args
 calls.append(args)
 return json.dumps(current[0])
ns=dict(json=json,subprocess=types.SimpleNamespace(check_output=fake),previous=previous,
 root=root,os=os,seed=seed,seed_hash=hashlib.sha256(seed.read_bytes()).hexdigest(),
 hashlib=hashlib,Path=Path,fmt=fmt)
exec(compile(ast.Module(body=[function],type_ignores=[]),'inspector-test','exec'),ns)
check=ns['inspect_reuse']
check(['docker'],{'SAFE':'1'})
cases=[('active','running',True),('foreign-token','token','wrong'),
 ('raised-memory','memory',13*1024**3),('swap','swap_total',13*1024**3),
 ('cpu','cpu_nano',2000000000),('network','network','host'),
 ('wrong-image','image','wrong'),('changed-cmd','cmd',['sh','-c','true']),
 ('wrong-workdir','workdir','/tmp'),('wrong-user','user','0:0'),
 ('wrong-driver','driver','overlay2'),('root-write','writable_bytes',1),
 ('missing-mount','mounts',[]),
 ('cache-env','selected_env',[None,'LAKE_CACHE_DIR=wrong','LAKE_ARTIFACT_CACHE=false','LEAN_NUM_THREADS=1'])]
for name,key,value in cases:
 current[0]=copy.deepcopy(baseline)
 current[0][key]=value
 try:
  check(['docker'],{'SAFE':'1'})
 except AssertionError:
  pass
 else:
  raise AssertionError('accepted '+name)
assert len(calls)==15
print('PASS: positive profile accepted;14 corrupt/foreign/unbounded profiles rejected;15 mocked inspect-only calls;no Docker start/build/write')

# Inspect generated transforms without executing the final bounded driver.
p=root/'scripts/v08-reuse-published.py'
tree=ast.parse(p.read_text())
assert isinstance(tree.body[-1],ast.Expr) and isinstance(tree.body[-1].value,ast.Call) and tree.body[-1].value.func.id=='exec'
tree.body.pop()
import sys
for arguments in [['Solidity.KeySort','Solidity.Lowering.V08.SourceFailureControls'],['--decision']]:
 saved_argv=sys.argv
 sys.argv=[str(p)]+arguments
 ns={'__file__':str(p),'__name__':'__generation_test__'}
 exec(compile(tree,str(p),'exec'),ns)
 sys.argv=saved_argv
 generated=ns['source']
 assert 'wall_limit_seconds = 600' in generated
 assert "'--memory', '12g'" in generated and "'--memory-swap', '12g'" in generated
 assert "'-e', 'LAKE_CACHE_DIR=', '-e', 'LAKE_ARTIFACT_CACHE=false'" in generated
 assert "cmd=docker+['start','--attach',previous['container']]" in generated
 assert "assert ordered==previous['modules']" in generated
 assert "assert cmd[-1]==previous['command'][-1]" in generated
 assert "assert configuration_before==previous['runtime_configuration']['sha256']" in generated
 assert "assert digest_if_file(root/path)==previous['source_sha256'][path]" in generated
 assert 'cleanup.ensure_stopped(docker, name,' not in generated
 assert "assert stat.st_ctime_ns <= cutoff" in generated
 assert "trace['outputs']['o']" in generated
 assert "completed_prefix=completed" in generated
print('PASS: both generated modes preserve bounds, exact configuration/command/closure, cache settings and cleanup identity; no driver/start/build executed')

# The final decision helper adds the newly completed Hashes dependency, without
# executing its driver. It retains the exact runtime/config/guard transform.
p=root/'scripts/v08-reuse-decision-complete.py'
tree=ast.parse(p.read_text());tree.body.pop()
saved_argv=sys.argv;sys.argv=[str(p),'--decision']
ns={'__file__':str(p),'__name__':'__complete_generation_test__'}
exec(compile(tree,str(p),'exec'),ns);sys.argv=saved_argv
generated=ns['source'];ast.parse(generated)
assert "for module in ordered[:-1]:" in generated
assert "'Solidity.Examples.DecisionHashes','Solidity.Examples.Decision'" in generated
assert "previous['modules']" in generated and 'wall_limit_seconds = 600' in generated
assert "cmd=docker+['start','--attach',previous['container']]" in generated
assert "assert configuration_before==previous['runtime_configuration']['sha256']" in generated
assert "assert cmd[-1]==previous['command'][-1]" in generated
print('PASS: complete-import helper retains original command, closure, configuration, cleanup and 600s bounds; generation only')

p=root/'scripts/v08-reuse-suite.py'
tree=ast.parse(p.read_text());tree.body.pop()
saved_argv=sys.argv;sys.argv=[str(p)]
ns={'__file__':str(p),'__name__':'__suite_generation_test__'}
exec(compile(tree,str(p),'exec'),ns);sys.argv=saved_argv
generated=ns['source'];ast.parse(generated)
assert "boundary=ordered.index('Solidity.TestSuite.Derived10')" in generated
assert "for module in ordered[:boundary]:" in generated
assert "assert ordered==previous['modules']" in generated
assert "assert cmd[-1]==previous['command'][-1]" in generated
assert 'wall_limit_seconds = 600' in generated
assert "cmd=docker+['start','--attach',previous['container']]" in generated
print('PASS: Suite generated profile preserves all targets, guards, completed-prefix certification and exact stopped runtime; NO START')

p=root/'scripts/v08-reuse-suite-complete.py'
tree=ast.parse(p.read_text());tree.body.pop()
saved_argv=sys.argv;sys.argv=[str(p)]
ns={'__file__':str(p),'__name__':'__suite_complete_generation_test__'}
exec(compile(tree,str(p),'exec'),ns);sys.argv=saved_argv
generated=ns['source'];ast.parse(generated)
assert "boundary=ordered.index('Solidity.TestSuite.Derived21')" in generated
assert "for module in ordered[:boundary]:" in generated
assert "assert ordered==previous['modules']" in generated
assert "assert cmd[-1]==previous['command'][-1]" in generated
assert 'wall_limit_seconds = 600' in generated
assert "cmd=docker+['start','--attach',previous['container']]" in generated
print('PASS: final Suite transformation retains exact original command, completed-prefix scope, cleanup and resource/time bounds; NO START')
