#!/usr/bin/env python3
"""Reuse only this turn's owned prefix gate, preserving old logs and budgets.
No allocation/deletion of containers, source, caches, receipts or sealed evidence.
"""
import ast, hashlib, json, os, runpy, subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parent.parent
seed=Path('/workspace/v08-world-lowering-evidence/v08-gate-718396-d77b835d.json')
previous=json.loads(seed.read_text())
assert previous['container']=='v08-gate-718396-d77b835d'
assert previous['git_head_at_check']=='5f2651bf6be91ecf2f29b57482a28dbe0083964e'
assert previous['modules'][-1]=='Solidity.Lowering.V08.PrefixControls'
assert not previous['full_gate'] and not previous['baseline']
assert previous['fresh_sort'] is None and previous['native_modules']==[]
seed_hash=hashlib.sha256(seed.read_bytes()).hexdigest()
assert hashlib.sha256(Path(previous['log']).read_bytes()).hexdigest()==previous['log_sha256']
plan_only=sys.argv[1:]==['--plan-only']
assert plan_only or sys.argv[1:]==[]
fmt="""{"id":{{json .Id}},"running":{{json .State.Running}},"exit":{{json .State.ExitCode}},"started":{{json .State.StartedAt}},"finished":{{json .State.FinishedAt}},"token":{{json (index .Config.Labels "org.solidity.v08.run")}},"memory":{{.HostConfig.Memory}},"swap_total":{{.HostConfig.MemorySwap}},"cpu_nano":{{.HostConfig.NanoCpus}},"network":{{json .HostConfig.NetworkMode}},"image":{{json .Config.Image}},"cmd":{{json .Config.Cmd}},"workdir":{{json .Config.WorkingDir}},"user":{{json .Config.User}},"driver":{{json .GraphDriver.Name}},"driver_data":{{json .GraphDriver.Data}},"writable_bytes":{{.SizeRw}},"mounts":{{json .Mounts}},"selected_env":[{{range .Config.Env}}{{if or (eq . "LAKE_CACHE_DIR=") (eq . "LAKE_ARTIFACT_CACHE=false") (eq . "LEAN_NUM_THREADS=1")}}{{json .}},{{end}}{{end}}null]}"""
def inspect_reuse(docker,env):
 value=json.loads(subprocess.check_output(docker+['inspect','--size','--format',fmt,previous['container']],env=env,text=True,timeout=30))
 assert not value['running'] and value['token']==previous['run_token']
 assert value['memory']==12884901888 and value['swap_total']==12884901888 and value['cpu_nano']==1000000000
 assert value['network']=='none' and value['driver']=='vfs' and value['writable_bytes']==0
 assert value['image']=='ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852'
 assert value['cmd']==['sh','-c',previous['command'][-1]]
 assert value['workdir']==str(root) and value['user']==str(os.getuid())+':'+str(os.getgid())
 assert set(value['selected_env'])=={None,'LAKE_CACHE_DIR=','LAKE_ARTIFACT_CACHE=false','LEAN_NUM_THREADS=1'}
 expected_mounts={}
 for index,part in enumerate(previous['command']):
  if part=='--mount':
   spec=previous['command'][index+1].split(',')
   fields=dict(piece.split('=',1) for piece in spec if '=' in piece)
   expected_mounts[fields['dst']]=(fields['src'],'readonly' not in spec)
 assert {m['Destination']:(m['Source'],m['RW']) for m in value['mounts']}==expected_mounts
 assert hashlib.sha256(seed.read_bytes()).hexdigest()==seed_hash
 assert hashlib.sha256(Path(previous['log']).read_bytes()).hexdigest()==previous['log_sha256']
 return value
saved=sys.argv
sys.argv=[str(root/'scripts/v08-no-artifact-cache.py'),'--self-test']
ns=runpy.run_path(str(root/'scripts/v08-no-artifact-cache.py'))
sys.argv=saved
source=ns['source']
def change(old,new,count=1):
 global source
 assert source.count(old)==count,(old,source.count(old))
 source=source.replace(old,new)
line="name = 'v08-gate-' + str(os.getpid()) + '-' + run_token[:8]"
change(line,line+"\nrun_token = reuse_previous['run_token']")
change("docker + ['top', name,","docker + ['top', reuse_previous['container'],")
change('cleanup.ensure_stopped(docker, name, run_token, log, env=env)',
 'cleanup.ensure_stopped(docker, reuse_previous["container"], run_token, log, env=env)',2)
injection="""
assert requested == ['Solidity.Lowering.V08.PrefixControls']
assert set(reuse_previous['modules']) <= set(ordered)
assert native_modules == set() and not full and not baseline and not fresh_sort
assert digest_if_file(run_config)==reuse_previous['runtime_configuration']['sha256']
certificate=json.loads((evidence/'v08-gate-704511-e74a9e12.json').read_text())
assert certificate['exit']==0 and certificate['runtime_configuration']['sha256']==configuration_before
assert certificate['tool_versions']==reuse_previous['tool_versions']
assert hashlib.sha256(Path(certificate['log']).read_bytes()).hexdigest()==certificate['log_sha256']
assert not certificate['resource_or_time_guard_stopped'] and certificate['source_unchanged']
assert digest_if_file(root/'lean-toolchain')==certificate['source_sha256']['lean-toolchain']
reuse_cached_outputs={}
validated_at=Path(certificate['log']).stat().st_mtime_ns
for module in set(ordered)-set(reuse_previous['modules']):
 path=str(graph.source(module).relative_to(root))
 assert digest_if_file(root/path)==certificate['source_sha256'][path]
 lib=root/'.lake/build/lib/lean'/Path(module.replace('.','/'))
 ir=root/'.lake/build/ir'/Path(module.replace('.','/'))
 artifacts=[lib.with_suffix(ext) for ext in ['.olean','.olean.hash','.ilean','.ilean.hash','.trace']]
 artifacts += [ir.with_suffix(ext) for ext in ['.c','.c.hash','.setup.json']]
 trace=json.loads(lib.with_suffix('.trace').read_text())
 assert trace['outputs']['o']==[lib.with_suffix('.olean.hash').read_text().strip()]
 assert trace['outputs']['i']==lib.with_suffix('.ilean.hash').read_text().strip()
 assert trace['outputs']['c']==ir.with_suffix('.c.hash').read_text().strip()
 metadata={}
 for artifact in artifacts:
  stat=artifact.stat()
  assert stat.st_ctime_ns <= validated_at, ('artifact changed after passing certificate',artifact)
  metadata[str(artifact)]=dict(bytes=stat.st_size,ctime_ns=stat.st_ctime_ns,sha256=digest_if_file(artifact))
 reuse_cached_outputs[module]=dict(source=path,source_sha256=digest_if_file(root/path),artifacts=metadata)
reuse_before=inspect_reuse(docker,env)
# The configured command and ALL original explicit targets are UNCHANGED.
# Its last target builds the current import closure; new imported prior-Audit
# modules are already source/config/toolchain-keyed compiled outputs.
assert reuse_previous['command'][-1].endswith(' build Solidity.Lowering.V08.PrefixControls; ')
(evidence/('prefix-reuse-'+name+'-before.json')).write_text(json.dumps(dict(
 seed=str(reuse_seed),seed_sha256=reuse_seed_hash,inspection=reuse_before,
 current_import_closure=ordered,previous_explicit_modules=reuse_previous['modules'],
 configured_command=reuse_previous['command'],warm_output_certificate=reuse_cached_outputs),indent=2)+'\\n')
cmd=docker+['start','--attach',reuse_previous['container']]
if reuse_plan_only:
 print(json.dumps(dict(mode='INSPECT_ONLY_NO_START',inspection=reuse_before,
  free_bytes=os.statvfs(root).f_bavail*os.statvfs(root).f_frsize),indent=2))
 raise SystemExit(0)
"""
change('cmd[-1] = script','cmd[-1] = script'+injection)
change('container=name)', 'container=reuse_previous["container"], reused_from=str(reuse_seed), '
 'configured_command=reuse_previous["command"], previous_explicit_modules=reuse_previous["modules"], '
 'inspection_before=reuse_before, inspection_after=inspect_reuse(docker,env), warm_output_certificate=reuse_cached_outputs)')
ast.parse(source)
sys.argv=[str(root/'scripts/v08-bounded.py'),'Solidity.Lowering.V08.PrefixControls']
exec(compile(source,str(root/'scripts/v08-bounded.py'),'exec'),dict(
 __name__='__main__',__file__=str(root/'scripts/v08-bounded.py'),
 reuse_previous=previous,reuse_seed=seed,reuse_seed_hash=seed_hash,
 reuse_plan_only=plan_only,inspect_reuse=inspect_reuse))
