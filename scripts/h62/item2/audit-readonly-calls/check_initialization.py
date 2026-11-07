#!/usr/bin/env python3
"""Guard erased initialization exhaustion and substituted dependency artifacts.

Isolated initialization extension with explicitly verified executed dependency reuse and the SAME joint client, at original C6 or
current source. No held Premises import, project-cache fallback, compiler success
or whole-goal/runtime acceptance. Run under the existing bounded writer runner.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[4]
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result
original=load('transport_original_helper',ROOT/'scripts/h62/item1/readonly-bind/check_original_callback.py')
joint=load('transport_joint_helper',ROOT/'scripts/h62/item1/readonly-bind/check_credit_joints.py')
current=load('transport_current_census',Path(__file__).with_name('current_dependencies.py'))
check,profile=original.check,original.profile
TARGET='Solidity.Lowering.Readonly.PrimitiveInitialization'
SOURCE='tests/h62/item2/audit-readonly-calls/InitializationWitnesses.lean'
PREFIX='Solidity.H62.ReadonlyAudit.InitializationWitnesses.'
SOURCE_PREFIX='Solidity.Lowering.Readonly.PrimitiveInitialization.'
INTERFACES=[SOURCE_PREFIX+n for n in ['zero_value','zero_values','exhausted_nonempty','exhausted_empty']]
NAMES=['zero_value_joint','zero_values_joint','exhausted_nonempty_joint','exhausted_empty_joint','pure_ne_timeout','initialized_observed','exhausted_observed','empty_observed','always_timeout_refused','empty_timeout_refused']
cache_module=load('initialization_dependency_cache',Path(__file__).with_name('verified_dependency_cache.py'))


def inventory(raw):
    if profile.imports(raw.decode())!=[TARGET]:raise ValueError('unadmitted witness import')
    rows=original.export.census.declarations_text(SOURCE,raw.decode())
    if [r['source_name'] for r in rows]!=[PREFIX+n for n in NAMES]:raise ValueError('witness declaration census drift')
    return rows


def select(frozen,captured,pins):
    rows=[r for r in frozen['declarations'] if r['source_name'] in INTERFACES]
    if len(rows)!=len(INTERFACES) or {r['source_name'] for r in rows}!=set(INTERFACES):raise ValueError('original interface membership mismatch')
    actual={}
    for path in sorted({r['file'] for r in rows}):
        raw=(captured/path).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=pins[path]['source_sha256']:raise ValueError('captured interface substitution')
        actual.update({r['source_name']:r for r in original.export.census.declarations_text(path,raw.decode())})
    for row in rows:
        if row['source_name'] not in actual or any(actual[row['source_name']][k]!=row[k] for k in ['signature_sha256','variable_context','visibility']):raise ValueError('frozen interface header/context drift')
    return {'base':original.BASE,'modules':[{'file':p} for p in sorted({r['file'] for r in rows})],'declarations':rows}


def compatible_toolchain(frozen,path):
    compared=path.read_bytes()
    if compared!=frozen:raise ValueError('frozen/current toolchain differs')
    return hashlib.sha256(frozen).hexdigest()


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--mode',choices=['frozen','current'],required=True);p.add_argument('--reviewed',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--parent',type=Path,required=True);args=p.parse_args()
    frozen=current.original.load_pinned(args.reviewed,current.REVIEWED_SHA)
    current.verify_frozen(frozen)
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    read=original.read_git if args.mode=='frozen' else lambda p:(ROOT/p).read_bytes()
    order,pins=original.snapshot(read,TARGET,out/'captured')
    cache=cache_module.Cache(type('Inputs',(),{'current':current,'original':original,'check':check}),args.parent,args.mode,pins,out/'cached-tools')
    selected=select(frozen,out/'captured',pins)
    raw=(ROOT/SOURCE).read_bytes();rows=inventory(raw);source_pin=hashlib.sha256(raw).hexdigest()
    toolchain_pin=compatible_toolchain(original.read_git('lean-toolchain'),ROOT/'lean-toolchain')
    protected={str(p):check.sha(p) for p in [*Path(__file__).parent.glob('*.py'),*(ROOT/'scripts/h62/item1/readonly-bind').glob('*.py'),*current.SCANNER.glob('*.py'),check.LEAN]}
    original.pin_authenticated_file(protected,args.reviewed,current.REVIEWED_SHA)
    original.pin_authenticated_file(protected,ROOT/'lean-toolchain',toolchain_pin)
    library=out/'library';library.mkdir();env=profile.isolated_environment(os.environ,library)
    sdk=subprocess.check_output([str(check.LEAN),'--print-prefix'],env=env,text=True).strip()
    if Path(sdk).resolve()!=check.LEAN.resolve().parent.parent:raise ValueError('SDK root mismatch')
    steps=[];artifacts={}
    def run(tag,source,artifact=None):
        cmd=[str(check.LEAN),'-j1','--tstack=131072','--root='+str(out/'staged')]
        if artifact:artifact.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(artifact)]
        cmd.append(str(source));log=out/(tag+'.log')
        with log.open('w') as stream:done=subprocess.run(cmd,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        data=log.read_bytes();steps.append({'command':cmd,'exit':done.returncode,'log':str(log),'sha256':hashlib.sha256(data).hexdigest()})
        if done.returncode:raise SystemExit('INITIALIZATION_FAIL '+str(log))
        return data.decode()
    for relative in order+[SOURCE]:
        module=relative[:-5] if relative in pins else 'InitializationWitnesses'
        source=out/'captured'/relative if relative in pins else ROOT/SOURCE
        staged=out/'staged'/(module+'.lean');artifact=library/(module+'.olean')
        record=cache.copy(relative,source,staged,artifact) if relative in pins else None
        if record is None:record=check.compile_staged(source,staged,artifact,lambda src,obj:run(module.replace('/','_'),src,obj))
        expected=pins[relative]['source_sha256'] if relative in pins else source_pin
        if record['source_sha256']!=expected:raise ValueError('source changed before compile')
        protected.update({str(source):expected,str(staged):expected,str(artifact):record['artifact_sha256']});artifacts[relative]=record
    probe=out/'staged/Probe.lean'
    probe.write_text('import InitializationWitnesses\n'+original.export.generate(selected)+''.join('#print axioms '+PREFIX+n+'\n' for n in NAMES))
    protected[str(probe)]=check.sha(probe)
    log=run('probe',probe);types=original.export.collect(log,selected);axioms=joint.parse_axioms(log,PREFIX,NAMES)
    expected={r['source_name']:r for r in selected['declarations']}
    for row in types['declarations']:
        if row['raw_type_sha256']!=expected[row['source_name']]['elaborated']['raw_type_sha256']:raise ValueError('exact original kernel type drift')
    (out/'types.json').write_text(json.dumps(types,indent=2)+'\n');protected[str(out/'types.json')]=check.sha(out/'types.json')
    for path,pin in pins.items():
        if hashlib.sha256(read(path)).hexdigest()!=pin['source_sha256']:raise ValueError('dependency drift')
    if (ROOT/SOURCE).read_bytes()!=raw:raise ValueError('joint source drift')
    cache.verify()
    check.verify_hashes(protected|{s['log']:s['sha256'] for s in steps})
    if subprocess.check_output([str(check.LEAN),'--print-prefix'],env=env,text=True).strip()!=sdk:raise ValueError('SDK root changed')
    receipt={'schema':1,'mode':args.mode,'base':original.BASE,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
             'source':SOURCE,'source_sha256':source_pin,'witness_declarations':rows,'project_order':order,'source_pins':pins,
             'artifacts':artifacts,'steps':steps,'axioms':axioms,'types_sha256':check.sha(out/'types.json'),
             'interface_names':INTERFACES,'interfaces':selected['declarations'],
             'dependency_reuse':cache.provenance(),'protected_sha256':protected,'sdk_root':sdk,'runtime_gate_pass':False,
             'boundary':'Inhabited primitive inputs and original theorem applications only; no compiler success or Source/world/native adequacy. Frozen/current exact types and dependencies checked separately.'}
    payload=(json.dumps(receipt,indent=2)+'\n').encode();(out/'receipt.json').write_bytes(payload)
    print('INITIALIZATION_PASS '+json.dumps({'mode':args.mode,'interfaces':len(INTERFACES),'witness_theorems':len(axioms),'project_modules':len(order),'receipt_sha256':hashlib.sha256(payload).hexdigest()}))


if __name__=='__main__':main()
