#!/usr/bin/env python3
"""Guard stale dependency reuse and a dropped V2 child's physical frame.
Authenticate the exact prior selected-call packet; rebuild current source/import
changes and ALL transitive consumers. Checked unchanged objects may be hard-linked,
never rewritten. This validates the typed-core void family, not full H121.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('native_frame_parent',Path(__file__).with_name('check_execution_call.py'))
legacy=importlib.util.module_from_spec(spec);spec.loader.exec_module(legacy)
m=legacy.m
PARENT_SHA='2e3bbd12e97267f8194116240901e323e8ddb4dab123ef81cf37538b72c597e2'
SOURCE='tests/h62/item2/audit-readonly-calls/NativeFrameTransport.lean'
PREFIX='Solidity.H62.ReadonlyCalls.NativeFrameTransport.'
NAMES=['lift_returned','compiled_outcomes','selected_success']
LOCAL=[('ExecutionReplies',m.SOURCE),('ExecutionCall',legacy.SOURCE),('CheckedExecutionCall',legacy.CHECKED_SOURCE)]

def digest(raw):return hashlib.sha256(raw).hexdigest()
def sha(path):return digest(Path(path).read_bytes())
def load_pinned(path,pin):
    raw=path.read_bytes()
    if digest(raw)!=pin:raise ValueError('unadmitted receipt bytes')
    return json.loads(raw)
def source_bytes(path,pin):
    raw=path.read_bytes()
    if digest(raw)!=pin:raise ValueError('source changed after admission: '+str(path))
    return raw
def current_closure():
    order,pins=m.profile.closure(ROOT,[m.TARGET,legacy.CHECKED_TARGET],{})
    if legacy.HELD in order:raise ValueError('held Premises dependency refused')
    return order,pins
def dirty_modules(order,pins,old):
    dirty=set()
    for file in order:
        dependencies={name.replace('.','/')+'.lean' for name in pins[file]['imports']}
        if old.get(file)!=pins[file] or dependencies & dirty:dirty.add(file)
    return dirty

def inventory(raw):
    if m.profile.imports(raw.decode())!=['CheckedExecutionCall']:raise ValueError('native frame import drift')
    rows=m.joint.export.census.declarations_text(SOURCE,raw.decode())
    if [r['source_name'] for r in rows]!=[PREFIX+n for n in NAMES]:raise ValueError('native frame theorem census drift')
    return rows

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--parent',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    parent=a.parent.resolve();receipt_path=parent/'receipt.json'
    r=load_pinned(receipt_path,PARENT_SHA);native=Path(r['parent']);nr_path=native/'receipt.json'
    nr=load_pinned(nr_path,r['parent_receipt_sha256'])
    raw=(ROOT/SOURCE).read_bytes();source_pin=digest(raw);rows=inventory(raw)
    local_pins={file:sha(ROOT/file) for _,file in LOCAL};local_pins[SOURCE]=source_pin
    order,pins=current_closure()
    old=nr['source_pins']|r['extra_source_pins']
    # Only live project source drift may differ from historical evidence. Its
    # authenticated captured bytes and prior object/log pins still must match.
    live_source_paths={str(ROOT/f) for f in old}
    def historical():
        for record in [nr,r]:
            for file,digest in record['protected_sha256'].items():
                if file not in live_source_paths and sha(file)!=digest:raise ValueError('historical evidence drift: '+file)
            for step in record['steps']:
                if step['exit']!=0 or sha(step['log'])!=step['sha256']:raise ValueError('historical failed/substituted step')
        for file,pin in old.items():
            captured=(parent/'staged'/file) if file in r['extra_artifacts'] else (native/'staged'/file)
            captured_raw=source_bytes(captured,pin['source_sha256'])
            if m.profile.imports(captured_raw.decode())!=pin['imports']:raise ValueError('captured old import drift')
    historical()
    dirty=dirty_modules(order,pins,old)
    out=a.output.resolve()
    if out.is_relative_to(ROOT):raise ValueError('evidence must stay private')
    out.mkdir(parents=True,exist_ok=False);library=out/'library';library.mkdir()
    env=m.profile.isolated_environment(os.environ,library)
    sdk=subprocess.check_output([str(m.check.LEAN),'--print-prefix'],env=env,text=True).strip()
    if sdk!=r['sdk_root'] or sdk!=nr['sdk_root']:raise ValueError('SDK root drift')
    protected={str(Path(__file__).resolve()):sha(__file__),str(ROOT/SOURCE):source_pin,str(receipt_path):PARENT_SHA,str(nr_path):r['parent_receipt_sha256']}
    protected.update({str(ROOT/f):pin['source_sha256'] for f,pin in pins.items()})
    protected.update({str(ROOT/file):pin for file,pin in local_pins.items()})
    expected_sources={file:pin['source_sha256'] for file,pin in pins.items()}|local_pins
    steps=[];artifacts={};reused={};rebuilt=[]
    def run(tag,source,artifact=None):
        cmd=[str(m.check.LEAN),'-j1','--tstack=131072','--root='+str(out/'staged')]
        if source.name=='TermSize.lean':cmd+=['-DElab.async=false']
        if artifact:cmd+=['-o',str(artifact)]
        cmd.append(str(source));log=out/(tag+'.log')
        with log.open('w') as stream:done=subprocess.run(cmd,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        payload=log.read_bytes();log_pin=digest(payload);protected[str(log)]=log_pin
        steps.append({'command':cmd,'exit':done.returncode,'log':str(log),'sha256':log_pin})
        if done.returncode:raise SystemExit('NATIVE_FRAME_FAIL '+str(log))
        return payload.decode()
    records=nr['artifacts']|r['extra_artifacts']
    def compile_one(module,file,previous=None,reuse=False):
        source=ROOT/file;staged=out/'staged'/(module+'.lean');artifact=library/(module+'.olean')
        staged.parent.mkdir(parents=True,exist_ok=True);artifact.parent.mkdir(parents=True,exist_ok=True)
        pin=expected_sources[file];raw=source_bytes(source,pin);staged.write_bytes(raw)
        if staged.read_bytes()!=raw:raise ValueError('staged source substitution')
        protected[str(staged)]=pin
        if reuse:
            oldobject=parent/'library'/(module+'.olean')
            if sha(oldobject)!=previous['artifact_sha256'] or pin!=previous['source_sha256']:raise ValueError('unverified object reuse')
            os.link(oldobject,artifact);reused[file]=previous['artifact_sha256']
        else:run(module.replace('/','_'),staged,artifact);rebuilt.append(file)
        record={'source_sha256':pin,'artifact_sha256':sha(artifact)}
        artifacts[file]=record;protected[str(artifact)]=record['artifact_sha256']
    for file in order:compile_one(file[:-5],file,records.get(file),file not in dirty and file in records)
    # All local proof consumers rebuild after the current project closure, so no
    # historical local artifact can hide a changed transitive dependency.
    for module,file in LOCAL:compile_one(module,file)
    compile_one('NativeFrameTransport',SOURCE)
    probe=out/'staged/NativeFrameProbe.lean';probe.write_text('import NativeFrameTransport\n'+''.join('#print axioms '+PREFIX+n+'\n' for n in NAMES));protected[str(probe)]=sha(probe)
    axioms=m.joint.parse_axioms(run('probe',probe),PREFIX,NAMES)
    historical();m.check.verify_hashes(protected)
    if current_closure()!=(order,pins):raise ValueError('current closure drift')
    result={'status':'pass','head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'parent_sha256':PARENT_SHA,'source':SOURCE,'source_sha256':source_pin,'project_order':order,'source_pins':pins,'changed_or_transitive':sorted(dirty),'rebuilt':rebuilt,'reused_objects':reused,'artifacts':artifacts,'theorems':rows,'axioms':axioms,'steps':steps,'protected_sha256':protected,'sdk_root':sdk,'original_obligations_discharged':0,'full_ro_adequacy':False,'runtime_gate_pass':False}
    (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print('NATIVE_FRAME_PASS reused='+str(len(reused))+' rebuilt='+str(len(rebuilt))+' theorems='+str(len(axioms)))
if __name__=='__main__':main()
