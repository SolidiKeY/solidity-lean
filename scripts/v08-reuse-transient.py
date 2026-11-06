#!/usr/bin/env python3
"""New leaf component over unchanged, certified warm dependencies; one cold chain.
Reuse exactly the existing ABI runtime command and every resource/cache guard.
"""
import ast,hashlib
from pathlib import Path
root=Path(__file__).resolve().parent.parent
NEW='Solidity.Lowering.V08.SourceTransient'
def validate_cold_chain(ordered,imports):
 assert imports(NEW)==['Solidity.Lowering.V08.SourceEnvironment']
 cold={NEW,'Solidity.Lowering.V08.SourceAbiControls','Solidity.Lowering.V08.Audit','Solidity.Lowering.V08.PrefixControls'}
 reached={NEW}
 for module in ordered:
  if any(dependency in reached for dependency in imports(module)):reached.add(module)
 assert reached==cold,('nonserial stale branch',reached^cold)
 for module in cold:
  assert len(set(imports(module))&cold)<=1,('parallel cold prerequisites',module)
 return cold
source=(root/'scripts/v08-reuse-abi.py').read_text()
assert hashlib.sha256(source.encode()).hexdigest()=='694b2d793740f5f120fba0969011be3bfafc7caa2474cd29ab10d3cf16624a34'
a="assert old <= set(ordered) and set(ordered)-old==prior | {core,controls}"
b="assert old <= set(ordered) and set(ordered)-old==prior | {core,controls,'Solidity.Lowering.V08.SourceTransient'}"
assert source.count(a)==1;source=source.replace(a,b)
a="assert set(imports(controls)) <= old | prior | {core}"
b="assert set(imports(controls)) <= old | prior | {core,'Solidity.Lowering.V08.SourceTransient'}"
assert source.count(a)==1;source=source.replace(a,b)
# Validate all warm sources/outputs before the unchanged command can start.
a='inspection=inspect_reuse(docker,env)'
b='''cold_chain=validate_cold_chain(ordered,graph.imports)
certificate_path=evidence/'v08-gate-10390-96c6cb08.json'
certificate=json.loads(certificate_path.read_text())
assert certificate['exit']==0 and certificate['source_unchanged'] and certificate['container_cleanup_verified']
assert not certificate['resource_or_time_guard_stopped']
assert certificate['runtime_configuration']['sha256']==configuration_before
assert certificate['tool_versions']==previous['tool_versions']
assert digest_if_file(Path(certificate['log']))==certificate['log_sha256']
assert set(ordered)==set(certificate['modules']) | {'Solidity.Lowering.V08.SourceTransient'}
cutoff=Path(certificate['log']).stat().st_mtime_ns
warm={}
for module in ordered:
 if module in cold_chain:continue
 path=str(graph.source(module).relative_to(root))
 assert digest_if_file(root/path)==certificate['source_sha256'][path],('changed warm source',module)
 rel=Path(module.replace('.','/'));lib=root/'.lake/build/lib/lean'/rel;ir=root/'.lake/build/ir'/rel
 files=[lib.with_suffix(ext) for ext in ['.olean','.olean.hash','.ilean','.ilean.hash','.trace']]
 files += [ir.with_suffix(ext) for ext in ['.c','.c.hash','.setup.json']]
 trace=json.loads(lib.with_suffix('.trace').read_text())
 assert trace['outputs']['o']==[lib.with_suffix('.olean.hash').read_text().strip()]
 assert trace['outputs']['i']==lib.with_suffix('.ilean.hash').read_text().strip()
 assert trace['outputs']['c']==ir.with_suffix('.c.hash').read_text().strip()
 metadata={}
 for artifact in files:
  info=artifact.stat();assert info.st_ctime_ns<=cutoff,('warm output changed after certificate',artifact)
  metadata[str(artifact)]=dict(bytes=info.st_size,ctime_ns=info.st_ctime_ns,sha256=digest_if_file(artifact))
 warm[module]=dict(source_sha256=digest_if_file(root/path),artifacts=metadata)
(evidence/(name+'-transient-warm.json')).write_text(json.dumps(dict(
 wrapper_sha256=digest_if_file(root/'scripts/v08-reuse-transient.py'),
 certificate=str(certificate_path),certificate_sha256=digest_if_file(certificate_path),
 cold_chain=sorted(cold_chain),warm=warm),indent=2)+'\\\\n')
inspection=inspect_reuse(docker,env)'''
assert source.count(a)==1;source=source.replace(a,b)
a=' validate_prior=validate_prior,validate_extension=validate_extension,source=source,seed=seed,seed_hash=seed_hash,inspect_reuse=inspect_reuse,decision=decision))'
assert source.count(a)==1;source=source.replace(a,' validate_cold_chain=validate_cold_chain,\n'+a)
ast.parse(source)
exec(compile(source,str(root/'scripts/v08-reuse-abi.py'),'exec'),dict(
 __name__='__main__',__file__=str(root/'scripts/v08-reuse-abi.py'),validate_cold_chain=validate_cold_chain))
