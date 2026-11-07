#!/usr/bin/env python3
"""Guard Source-name-only selection and the empty-input frame shortcut.
Merge exactly authenticated native-frame and Source-read parents. Reuse only
unchanged source/import/dependency objects, compile new leaves, then seal actual
Source/selected-void witness and kernel probe logs. No held Premises or H121 claim.
"""
import argparse
import importlib.util
import importlib.machinery
import hashlib
import json
import os
from pathlib import Path
import subprocess
import types
ROOT=Path(__file__).resolve().parents[4]
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
# The CLI entry/Python runtime remain trusted bootstrap inputs. Repository
# helpers bypass pyc and compile the exact retained source buffers below.
LOADED_HELPER_BYTES={}
_original_get_code=importlib.machinery.SourceFileLoader.get_code
def retained_get_code(loader,name):
    file=Path(loader.path).resolve()
    if not file.is_relative_to(ROOT/'scripts'):return _original_get_code(loader,name)
    raw=file.read_bytes()
    if file in LOADED_HELPER_BYTES and LOADED_HELPER_BYTES[file]!=raw:
        raise ValueError('helper changed between imports')
    LOADED_HELPER_BYTES[file]=raw
    return compile(raw,str(file),'exec',dont_inherit=True)
importlib.machinery.SourceFileLoader.get_code=retained_get_code
try:
    frame=load('source_void_frame','check_native_frame.py');m=frame.m
    cache=load('source_void_cache','verified_dependency_cache.py')
finally:
    importlib.machinery.SourceFileLoader.get_code=_original_get_code
NATIVE_SHA='819a221faf4a57c37ef4f30997b470b1c67126ae7d9adfc11ae0ea51ca3d4bba'
SOURCE_SHA='de296db73898608cd3062f15a4e8a2d9c734fb17ed7cbebe425f104e596df1e8'
HISTORICAL='b099c40125795ce00cfa39c1df48fe5f76925a40'
SOURCE='tests/h62/item2/audit-readonly-calls/SourceVoidSelection.lean'
PREFIX='Solidity.H62.ReadonlyCalls.SourceVoidSelection.'
NAMES=['body_derived','signature','body_pair','instance_selected','function_selected','resolved_body','selector_length','source_dispatch','source_call','undeployed_refused','zero_horizon','wrong_selector','prepared','prepared_entry','prepared_input','nonempty_store','paired_execution']
LOCAL=frame.LOCAL+[('NativeFrameTransport',frame.SOURCE)]

def closure():
    order,pins=m.profile.closure(ROOT,[m.TARGET,frame.legacy.CHECKED_TARGET,'Solidity.Source.SemanticsExamples'],{})
    if frame.legacy.HELD in order:raise ValueError('held Premises dependency refused')
    return order,pins

def inventory(raw):
    if m.profile.imports(raw.decode())!=['NativeFrameTransport','Solidity.Source.SemanticsExamples']:raise ValueError('Source void import drift')
    rows=m.joint.export.census.declarations_text(SOURCE,raw.decode())
    if [r['source_name'] for r in rows]!=[PREFIX+n for n in NAMES]:raise ValueError('Source void theorem inventory drift')
    return rows

def capture_tools(roots,out,require_loaded=True):
    """Seal retained helper load buffers; the own CLI bootstrap is observed."""
    queue=list(roots);seen=set();files={Path(__file__).resolve()}
    while queue:
        module=queue.pop()
        if id(module) in seen:continue
        seen.add(id(module));file=getattr(module,'__file__',None)
        if not file:continue
        file=Path(file).resolve()
        if not file.is_relative_to(ROOT/'scripts'):continue
        files.add(file)
        queue.extend(value for value in vars(module).values() if isinstance(value,types.ModuleType))
    pins={};snapshots={}
    for file in sorted(files):
        own=file==Path(__file__).resolve()
        if require_loaded and not own and file not in LOADED_HELPER_BYTES:
            raise ValueError('loaded helper has no retained execution buffer')
        raw=LOADED_HELPER_BYTES[file] if file in LOADED_HELPER_BYTES else file.read_bytes()
        if file.read_bytes()!=raw:raise ValueError('helper changed after retained load')
        pin=frame.digest(raw);saved=out/'helper-sources'/file.relative_to(ROOT)
        saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(raw)
        if saved.read_bytes()!=raw:raise ValueError('helper snapshot replacement')
        pins[str(file)]=pin;pins[str(saved)]=pin;snapshots[str(file)]={'sha256':pin,'saved':str(saved),'kind':'retained-before-helper-execution' if file in LOADED_HELPER_BYTES else 'trusted-bootstrap-or-synthetic-source-observation'}
    return pins,snapshots

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--native',type=Path,required=True);p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    native=a.native.resolve();source=a.source.resolve();out=a.output.resolve()
    if out.is_relative_to(ROOT):raise ValueError('evidence must stay private')
    nr=frame.load_pinned(native/'receipt.json',NATIVE_SHA);sr=frame.load_pinned(source/'receipt.json',SOURCE_SHA)
    if nr['status']!='pass' or sr['mode']!='current' or sr['base']!=m.joint.original.BASE:raise ValueError('parent status/mode mismatch')
    out.mkdir(parents=True,exist_ok=False);library=out/'library';library.mkdir()
    tool_pins,tool_snapshots=capture_tools([frame,cache],out)
    raw=(ROOT/SOURCE).read_bytes();source_pin=frame.digest(raw);rows=inventory(raw)
    order,pins=closure();old=dict(sr['source_pins'])
    for file,pin in nr['source_pins'].items():
        if file in old and old[file]!=pin:raise ValueError('conflicting parent source/import pins')
        old[file]=pin
    dirty=frame.dirty_modules(order,pins,old)
    # Source-only parent also contains unselected declarations: verify ALL of
    # them, rather than weakening admission to the selected overlap.
    for record in [nr,sr]:
        for file,pin in record['source_pins'].items():
            raw_parent=frame.source_bytes(ROOT/file,pin['source_sha256'])
            if m.profile.imports(raw_parent.decode())!=pin['imports']:raise ValueError('parent import drift')
    historical={}
    def parents():
        if frame.sha(native/'receipt.json')!=NATIVE_SHA or frame.sha(source/'receipt.json')!=SOURCE_SHA:raise ValueError('parent receipt replacement')
        m.check.verify_hashes(nr['protected_sha256'])
        recovered,snapshots=cache.authenticate_tools(ROOT,HISTORICAL,sr['protected_sha256'],out/'historical-tools')
        historical.update(snapshots);m.check.verify_hashes(recovered)
        for root,record in [(native,nr),(source,sr)]:
            for step in record['steps']:
                if step['exit']!=0 or frame.sha(step['log'])!=step['sha256']:raise ValueError('parent failed/log substitution')
            for file in record['project_order']:
                if frame.sha(root/'library'/(file[:-5]+'.olean'))!=record['artifacts'][file]['artifact_sha256']:raise ValueError('parent object drift')
    parents()
    env=m.profile.isolated_environment(os.environ,library)
    sdk=subprocess.check_output([str(m.check.LEAN),'--print-prefix'],env=env,text=True).strip()
    if sdk!=nr['sdk_root'] or sdk!=sr['sdk_root']:raise ValueError('SDK mismatch')
    protected=tool_pins|{str(ROOT/SOURCE):source_pin,str(native/'receipt.json'):NATIVE_SHA,str(source/'receipt.json'):SOURCE_SHA}
    protected.update({str(ROOT/f):pin['source_sha256'] for f,pin in pins.items()})
    local_pins={file:frame.sha(ROOT/file) for _,file in LOCAL};local_pins[SOURCE]=source_pin
    protected.update({str(ROOT/f):pin for f,pin in local_pins.items()})
    expected={f:pin['source_sha256'] for f,pin in pins.items()}|local_pins
    artifacts={};reused={};rebuilt=[];steps=[]
    def run(tag,staged,artifact=None):
        cmd=[str(m.check.LEAN),'-j1','--tstack=131072','--root='+str(out/'staged')]
        if staged.name=='TermSize.lean':cmd+=['-DElab.async=false']
        if artifact:cmd+=['-o',str(artifact)]
        cmd.append(str(staged));log=out/(tag+'.log')
        with log.open('w') as stream:done=subprocess.run(cmd,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        payload=log.read_bytes();pin=frame.digest(payload);protected[str(log)]=pin
        steps.append({'command':cmd,'exit':done.returncode,'log':str(log),'sha256':pin})
        if done.returncode:raise SystemExit('SOURCE_VOID_FAIL '+str(log))
        return payload.decode()
    def module(module,file,parent=None):
        staged=out/'staged'/(module+'.lean');artifact=library/(module+'.olean')
        staged.parent.mkdir(parents=True,exist_ok=True);artifact.parent.mkdir(parents=True,exist_ok=True)
        raw=frame.source_bytes(ROOT/file,expected[file]);staged.write_bytes(raw)
        if staged.read_bytes()!=raw:raise ValueError('staged source replacement')
        protected[str(staged)]=expected[file]
        if parent:
            root,record=parent;oldobject=root/'library'/(module+'.olean')
            if record['source_sha256']!=expected[file] or frame.sha(oldobject)!=record['artifact_sha256']:raise ValueError('unverified reuse')
            os.link(oldobject,artifact);reused[file]={'parent':str(root),'sha256':record['artifact_sha256']}
        else:run(module.replace('/','_'),staged,artifact);rebuilt.append(file)
        artifacts[file]={'source_sha256':expected[file],'artifact_sha256':frame.sha(artifact)}
        protected[str(artifact)]=artifacts[file]['artifact_sha256']
    for file in order:
        parent=None
        if file not in dirty:
            root,record=(native,nr) if file in nr['source_pins'] else (source,sr)
            parent=(root,record['artifacts'][file])
        module(file[:-5],file,parent)
    local_dirty=bool(dirty & set(nr['source_pins']))
    for name,file in LOCAL:module(name,file,None if local_dirty else (native,nr['artifacts'][file]))
    module('SourceVoidSelection',SOURCE)
    probe=out/'staged/SourceVoidProbe.lean';probe.write_text('import SourceVoidSelection\n'+''.join('#print axioms '+PREFIX+n+'\n' for n in NAMES));protected[str(probe)]=frame.sha(probe)
    axioms=m.joint.parse_axioms(run('probe',probe),PREFIX,NAMES)
    parents();m.check.verify_hashes(protected)
    if closure()!=(order,pins):raise ValueError('current source/import closure drift')
    receipt={'status':'pass','head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'source':SOURCE,'source_sha256':source_pin,'native_receipt_sha256':NATIVE_SHA,'source_receipt_sha256':SOURCE_SHA,'source_pins':pins,'project_order':order,'changed_or_new':sorted(dirty),'reused':reused,'rebuilt':rebuilt,'artifacts':artifacts,'steps':steps,'protected_sha256':protected,'historical_tools':historical,'helper_source_bindings':tool_snapshots,'helper_binding_boundary':'Repository helper buffers retained before execution; CLI bootstrap/Python runtime/stdlib trusted; no remote attestation','theorems':rows,'axioms':axioms,'sdk_root':sdk,'original_obligations_discharged':0,'full_ro_adequacy':False,'runtime_gate_pass':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('SOURCE_VOID_PASS modules='+str(len(order))+' reused='+str(len(reused))+' rebuilt='+str(len(rebuilt))+' theorems='+str(len(axioms)))
if __name__=='__main__':main()
