#!/usr/bin/env python3
"""Read-only actual cold-chain and corruption/profile controls; no starts/builds."""
import ast,copy,hashlib,sys,importlib.util
from pathlib import Path
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parent.parent;p=root/'scripts/v08-reuse-transient.py';tree=ast.parse(p.read_text())
fn=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='validate_cold_chain')
NEW='Solidity.Lowering.V08.SourceTransient';ns={'NEW':NEW};exec(compile(ast.Module(body=[fn],type_ignores=[]),'cold-chain','exec'),ns);check=ns['validate_cold_chain']
spec=importlib.util.spec_from_file_location('v08_graph',root/'scripts/v08-build-graph.py');graphmod=importlib.util.module_from_spec(spec);spec.loader.exec_module(graphmod);g=graphmod.SourceGraph(root)
ordered=g.closure(['Solidity.KeySort','Solidity.Lowering.V08.PrefixControls']);deps={m:g.imports(m) for m in ordered};cold=check(ordered,deps.__getitem__);assert len(cold)==4
bad=[]
x=copy.deepcopy(deps);x[NEW].append('Foreign');bad.append(('new-import',x))
x=copy.deepcopy(deps);x['Solidity.Lowering.V08.SourceKeccak'].append(NEW);bad.append(('stale-independent-branch',x))
x=copy.deepcopy(deps);x['Solidity.Lowering.V08.Audit'].append(NEW);bad.append(('parallel-cold-prerequisites',x))
x=copy.deepcopy(deps);x['Solidity.Lowering.V08.SourceAbiControls']=[m for m in x['Solidity.Lowering.V08.SourceAbiControls'] if m!=NEW];bad.append(('missing-chain',x))
for name,deps2 in bad:
 try:check(ordered,deps2.__getitem__)
 except AssertionError:pass
 else:raise AssertionError('accepted '+name)
assert isinstance(tree.body[-1],ast.Expr);tree.body.pop();ns={'__file__':str(p)};exec(compile(tree,str(p),'exec'),ns)
abi=ast.parse(ns['source']);assert isinstance(abi.body[-1],ast.Expr);abi.body.pop();saved=sys.argv;sys.argv=[str(p)];ns2={'__file__':str(root/'scripts/v08-reuse-abi.py'),'validate_cold_chain':check};exec(compile(abi,'inert-abi','exec'),ns2);sys.argv=saved
source=ns2['source'];ast.parse(source)
for text in ["'--memory', '12g'","'--memory-swap', '12g'","'--cpus', '1'","'-e', 'LEAN_NUM_THREADS=1'","'-e', 'LAKE_CACHE_DIR=', '-e', 'LAKE_ARTIFACT_CACHE=false'","wall_limit_seconds = 600","cmd=docker+['start','--attach',previous['container']]","cmd[-1]=previous['command'][-1]","assert configuration_before==previous['runtime_configuration']['sha256']","if module!='Solidity.Lowering.V08.Audit': assert digest_if_file",'cold_chain=validate_cold_chain','warm output changed after certificate',"certificate['source_sha256'][path]",'trace[\'outputs\'][\'o\']',"wrapper_sha256=digest_if_file(root/'scripts/v08-reuse-transient.py')"]:
 assert text in source,text
print('PASS: actual'+str(len(ordered))+'-module graph has single4-module cold chain;4 parallel/stale/foreign/missing-chain corruptions; original source/resource/cache/command guards and certified warm artifact/source checks retained; no Docker/start/build/write')

# Actual final-level serialized certificate, not merely an intermediate AST.
import json
warm_path=Path('/workspace/v08-world-lowering-evidence/v08-gate-30988-47169f59-transient-warm.json')
warm=json.loads(warm_path.read_bytes())
assert warm['wrapper_sha256']==hashlib.sha256(p.read_bytes()).hexdigest()
assert set(warm['cold_chain'])==cold and len(warm['warm'])==len(ordered)-len(cold)
assert warm['certificate_sha256']==hashlib.sha256(Path(warm['certificate']).read_bytes()).hexdigest()
print('PASS: actual generated warm certificate parses; wrapper/certificate hashes and135 warm sources/singlecoldchain bind; no start/build/write')
