#!/usr/bin/env python3
"""Guard syntax-only producer candidates and assumed outputs replacing kernel consumers.
Checks nine imported theorem identities/types/direct source positions plus actual
success/revert consumer axiom sets. Standard current-tree Lake dependencies are
cached inputs, not an independent fresh build or resolved Source/P1 adequacy.
Run under bounded.py; no held Premises closure is permitted.
"""
import argparse
import ast
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[4]
SOURCE='tests/h62/item2/audit-readonly-calls/CompilerOutcomeWitnesses.lean'
PREFIX='Solidity.H62.ReadonlyAudit.CompilerOutcomeWitnesses.'
SURFACE_SHA='2dc0d6b6d64b1c3e0c8ba89e6b05be9af41e2205210b7ad04701b2109e361637'
LEAN=Path('/workspace/.setup/tools/lean-4.24.0-linux/bin/lean')
LAKE=LEAN.with_name('lake')
ALLOWED={'propext','Classical.choice','Quot.sound'}

def digest(raw):return hashlib.sha256(raw).hexdigest()
def sha(path):return digest(Path(path).read_bytes())
def pinned(path,pin):
    raw=path.read_bytes()
    if digest(raw)!=pin:raise ValueError('unadmitted receipt or input: '+str(path))
    return json.loads(raw)
def verify(pins):
    for path,pin in pins.items():
        if sha(path)!=pin:raise ValueError('protected compiler input drift: '+path)
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def byte_position(raw,position):
    line,column=position['line'],position['column'];lines=raw.decode().split('\n')
    if type(line)!=int or type(column)!=int or not 1<=line<=len(lines) or not 0<=column<=len(lines[line-1]):raise ValueError('invalid compiler position')
    return len(('\n'.join(lines[:line-1])+('\n' if line>1 else '')+lines[line-1][:column]).encode())

def bind_rows(candidates,syntax,types,locations,sources):
    wanted={r['candidate_source_name']:r for r in candidates}
    if len(wanted)!=9 or len(types)!=9 or len(locations)!=9:raise ValueError('producer membership drift')
    bytype={r['source_name']:r for r in types};byloc={r['source_name']:r for r in locations}
    if set(bytype)!=set(wanted) or len(bytype)!=len(types) or set(byloc)!=set(wanted) or len(byloc)!=len(locations):raise ValueError('duplicate/missing kernel record')
    astrows={r['path']:r['records'] for r in syntax};out=[]
    for name,row in wanted.items():
        t=bytype[name];loc=byloc[name];module=row['file'][:-5].replace('/','.')
        if t['kernel_name']!=name or t['module']!=module or not t['raw_type_expr'] or not t['pretty_type']:raise ValueError('kernel/module/type mismatch')
        matches=[r for r in astrows[row['file']] if r.get('name')==name.rsplit('.',1)[-1] and r.get('signature_range')==row['signature_range']]
        if len(matches)!=1:raise ValueError('ambiguous/missing syntax name position')
        raw=sources[row['file']];start=byte_position(raw,loc['start']);end=byte_position(raw,loc['end'])
        if {'start':start,'end':end}!=matches[0]['name_range'] or raw[start:end].decode()!=row['name_span']:raise ValueError('direct source selection mismatch')
        out.append({'source_name':name,'kernel_name':t['kernel_name'],'module':module,'file':row['file'],
                    'source_sha256':digest(raw),'surface_header_sha256':row['header_span_sha256'],
                    'selection':loc,'type':t,'raw_type_sha256':digest(t['raw_type_expr'].encode()),
                    'status':'direct-current-source-kernel-type-link','ownership_verified':False})
    return out

def parse_axioms(log,names):
    records=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",log)
    if len(records)!=len(names) or {n for n,_ in records}!=set(names):raise ValueError('axiom membership drift')
    result={n:[x.strip() for x in raw.split(',') if x.strip()] for n,raw in records}
    if any(set(x)-ALLOWED for x in result.values()):raise ValueError('unexpected compiler axiom')
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--surface',type=Path,required=True);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    paths=[*ROOT.joinpath('scripts/h62').rglob('*.py'),*ROOT.joinpath('tests/h62').rglob('*.py'),ROOT/SOURCE,LEAN,LAKE,Path(sys.executable),ROOT/'lean-toolchain',ROOT/'lakefile.toml',ROOT/'tests/h62/item2/audit-readonly-calls/coverage.json']
    pins={str(x):sha(x) for x in paths};raw_client=(ROOT/SOURCE).read_bytes()
    if digest(raw_client)!=pins[str(ROOT/SOURCE)]:raise ValueError('consumer source changed')
    profile=load('compiler_dependency_profile',ROOT/'scripts/h62/item1/readonly-bind/check_capture_fixtures.py')
    surface=pinned(args.surface/'receipt.json',SURFACE_SHA);pins[str(args.surface/'receipt.json')]=SURFACE_SHA
    requested=pinned(args.surface/'requested.json',surface['protected_sha256'][str(args.surface/'requested.json')])
    syntax=pinned(args.surface/'raw-parser.json',surface['protected_sha256'][str(args.surface/'raw-parser.json')])
    for name in ['requested.json','raw-parser.json','original-preservation.json']:pins[str(args.surface/name)]=surface['protected_sha256'][str(args.surface/name)]
    original=pinned(args.surface/'original-preservation.json',pins[str(args.surface/'original-preservation.json')])
    if original['original_count']!=792 or len(original['identities'])!=792 or len({(r['file'],r['source_name']) for r in original['identities']})!=792:raise ValueError('original792 membership drift')
    if pins[str(ROOT/'tests/h62/item2/audit-readonly-calls/coverage.json')]!=original['coverage_sha256']:raise ValueError('original coverage drift')
    if surface['status']!='pass' or surface['kernel_binding'] or len(requested)!=9:raise ValueError('bad surface scope')
    modules=sorted({r['file'][:-5].replace('/','.') for r in requested})
    order,source_pins=profile.closure(ROOT,modules,{})
    sources={}
    for path,pin in source_pins.items():
        raw=(ROOT/path).read_bytes()
        if digest(raw)!=pin['source_sha256']:raise ValueError('dependency source changed')
        saved=out/'sources'/path;saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(raw)
        pins[str(ROOT/path)]=pin['source_sha256'];pins[str(saved)]=pin['source_sha256']
        sources[path]=raw
    for row in requested:
        path=row['file'];old=args.surface/'sources'/path
        pin=surface['protected_sha256'][str(old)]
        if sources[path]!=old.read_bytes() or sha(old)!=pin:raise ValueError('producer source differs from parsed surface')
        pins[str(old)]=pin
    export=ROOT/'scripts/h62/item2/audit-readonly-calls/export_signatures.py';export_raw=export.read_bytes()
    if digest(export_raw)!=pins[str(export)]:raise ValueError('export helper changed before staging')
    helper=[n for n in ast.parse(export_raw).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='HELPER' for t in n.targets)]
    if len(helper)!=1:raise ValueError('export helper ambiguity')
    helper=ast.literal_eval(helper[0].value)
    names=[PREFIX+n for n in re.findall(r'^theorem ([A-Za-z_][A-Za-z_0-9]*)',raw_client.decode(),re.M)]
    if len(names)!=14 or len(set(names))!=14:raise ValueError('consumer theorem inventory drift')
    staged=out/'staged';staged.mkdir();query=staged/'CompilerConsumerProbe.lean'
    commands=[]
    for row in requested:
        name=row['candidate_source_name'];module=row['file'][:-5].replace('/','.')
        commands.append(f'run_cmd exportOne `{name} `{module} false')
        commands.append('run_cmd do\n  let some r ← findDeclarationRangesCore? `'+name+' | throwError "missing direct producer range"\n  logInfo m!"H62-PRODUCER-RANGE { (Json.mkObj [(\"source_name\",toJson '+json.dumps(name)+'),(\"start\",toJson r.selectionRange.pos),(\"end\",toJson r.selectionRange.endPos)]).compress }"')
    allnames=names+[r['candidate_source_name'] for r in requested]
    text='import Lean\nimport Solidity.Backend.AbiWorld.PublicCompilerTotalControls\n'+raw_client.decode()+'\n'+helper+'\n'+'\n'.join(commands)+'\nend Solidity.H62.ReadonlyAudit.Metadata\n'+''.join('#print axioms '+n+'\n' for n in allnames)
    query.write_text(text);pins[str(query)]=digest(text.encode())
    config_raw=(ROOT/'lakefile.toml').read_bytes()
    if digest(config_raw)!=pins[str(ROOT/'lakefile.toml')]:raise ValueError('Lake config changed before staging')
    config=out/'lakefile.toml';config.write_bytes(b'weakLeanArgs = ["-j1"]\n'+config_raw);pins[str(config)]=sha(config)
    env=profile.isolated_environment(os.environ,out/'unused-private');env['LAKE_CACHE_DIR']='/workspace/.setup/cache/lake';env['XDG_CACHE_HOME']='/workspace/.setup/cache'
    # Lake supplies current dependency paths; the unused private path is not an artifact fallback.
    sdk=subprocess.check_output([str(LEAN),'--print-prefix'],env=env,text=True).strip()
    if Path(sdk).resolve()!=LEAN.resolve().parent.parent:raise ValueError('SDK root mismatch')
    verify(pins);cmd=[str(LAKE),'-f',str(config),'lean',str(query),'--','--tstack=131072','-j1','--root='+str(staged)]
    log=out/'query.log'
    with log.open('w') as stream:r=subprocess.run(cmd,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
    data=log.read_bytes();pins[str(log)]=digest(data)
    if r.returncode:raise ValueError('compiler kernel probe failed: '+str(log))
    types=[];locations=[]
    for line in data.decode().splitlines():
        if line.startswith('H62-SIGNATURE '):types.append(json.loads(line[len('H62-SIGNATURE '):]))
        if line.startswith('H62-PRODUCER-RANGE '):locations.append(json.loads(line[len('H62-PRODUCER-RANGE '):]))
    bound=bind_rows(requested,syntax,types,locations,sources);axioms=parse_axioms(data.decode(),allnames)
    for name,value in [('kernel-bindings.json',bound),('axioms.json',axioms)]:
        file=out/name;file.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n');pins[str(file)]=sha(file)
    observations=[]
    cache=Path(env['LAKE_CACHE_DIR'])/'artifacts'
    for relative in order:
        module=relative[:-5];trace=ROOT/'.lake/build/lib/lean'/(module+'.trace')
        observation={'source':relative,'source_sha256':source_pins[relative]['source_sha256'],'actual_loader_bytes_attested':False,'objects':[]}
        if trace.exists():
            trace_raw=trace.read_bytes();pins[str(trace)]=digest(trace_raw)
            observation['trace']=str(trace);observation['trace_sha256']=digest(trace_raw)
            outputs=json.loads(trace_raw).get('outputs',{})
            for h in outputs.get('o',[]):
                for candidate in sorted(cache.glob(str(h)+'.olean*')):
                    pins[str(candidate)]=sha(candidate);observation['objects'].append({'path':str(candidate),'sha256':pins[str(candidate)],'kind':'Lake-cache-output-candidate'})
        local=ROOT/'.lake/build/lib/lean'/(module+'.olean')
        if local.exists():
            pins[str(local)]=sha(local);observation['objects'].append({'path':str(local),'sha256':pins[str(local)],'kind':'current-build-object'})
        observations.append(observation)
    observed=out/'artifact-observations.json';observed.write_text(json.dumps(observations,indent=2)+'\n');pins[str(observed)]=sha(observed)
    if profile.closure(ROOT,modules,{})!=(order,source_pins):raise ValueError('dependency graph drift')
    verify(pins)
    if subprocess.check_output([str(LEAN),'--print-prefix'],env=env,text=True).strip()!=sdk:raise ValueError('SDK root changed')
    coverage=ROOT/'tests/h62/item2/audit-readonly-calls/coverage.json'
    receipt={'schema':1,'status':'pass','head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'command':cmd,'exit':r.returncode,'log':str(log),'log_sha256':digest(data),'sdk_root':sdk,'source':SOURCE,'source_sha256':digest(raw_client),'project_order':order,'source_pins':source_pins,'protected_sha256':pins,'producer_kernel_links':len(bound),'consumer_axiom_records':len(names),'producer_axiom_records':len(requested),'coverage_sha256':sha(coverage),'original_preservation_sha256':pins[str(args.surface/'original-preservation.json')],'artifact_observations':'post-query snapshots; no source-to-object or loader-byte attestation','original_obligations':792,'original_credit':0,'runtime_gate_pass':False,'boundary':'Current basic public compiler/intrinsic programs and data-free outcomes only. Lake caches used; no independently fresh dependency proof/SDK certification, resolved Source/world/physical P1 or gas/fork adequacy.'}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','producer_kernel_links','consumer_axiom_records','producer_axiom_records','original_credit']}))
if __name__=='__main__':main()
