#!/usr/bin/env python3
"""Guard step-only, stale or source-named evidence replacing an actual caller image.

Reuse only the exact freshly checked native parent, verify all current source,
object, tool and log pins, then check the additive generic caller module. This
is target-only transport; --checked additionally retains the existing typed-core
void compiler family's full Returned contract. Neither is resolved Source/world
or full P1 adequacy.
Use the existing bounded runner for exclusive writer/resource bounds.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[4]
helper=ROOT/'scripts/h62/item2/audit-readonly-calls/check_execution_replies.py'
spec=importlib.util.spec_from_file_location('call_native_helper',helper)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
PARENT_SHA='003afb9eb76e4c8a9e5db8b3fb14914aa62eee0b27069d1fd7c78b1689c0329f'
SOURCE='tests/h62/item2/audit-readonly-calls/ExecutionCall.lean'
PREFIX='Solidity.H62.ReadonlyCalls.ExecutionCall.'
CHECKED_SOURCE='tests/h62/item2/audit-readonly-calls/CheckedExecutionCall.lean'
CHECKED_PREFIX='Solidity.H62.ReadonlyCalls.CheckedExecutionCall.'
CHECKED_TARGET='Solidity.Backend.InternalFlow.RuntimeFrameP1V2CallAgreementControls'
HELD='Solidity/Backend/WorldCalls/Premises.lean'
CHECKED_NAMES=['entry_stack','compiled_native','prepared_empty','prepared_entry','selected_success','selected_revert']
NAMES=['prefix_run','input_read','callIn_stack','run_code','storeMem_above','memory_outside',
       'native_call','funded_native','native_echo','native_revert','poor_native']


def read_parent(path):
    raw=path.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=PARENT_SHA:raise ValueError('unadmitted native caller parent')
    return json.loads(raw)


def verify_parent(parent,receipt):
    if m.profile.closure(ROOT,[m.TARGET],{})!=(receipt['project_order'],receipt['source_pins']):
        raise ValueError('native caller parent source/import drift')
    m.check.verify_hashes(receipt['protected_sha256']|{s['log']:s['sha256'] for s in receipt['steps']})
    if m.check.sha(ROOT/m.SOURCE)!=receipt['artifacts'][m.SOURCE]['source_sha256']:
        raise ValueError('native caller helper source drift')
    for relative,record in receipt['artifacts'].items():
        module=relative[:-5] if relative!=m.SOURCE else 'ExecutionReplies'
        if m.check.sha(parent/'library'/(module+'.olean'))!=record['artifact_sha256']:
            raise ValueError('native caller parent object substitution')


def inventory(raw,checked=False):
    imports=['ExecutionCall',CHECKED_TARGET] if checked else ['ExecutionReplies']
    source=CHECKED_SOURCE if checked else SOURCE
    prefix=CHECKED_PREFIX if checked else PREFIX;names=CHECKED_NAMES if checked else NAMES
    if m.profile.imports(raw.decode())!=imports:raise ValueError('unadmitted caller import')
    rows=m.joint.export.census.declarations_text(source,raw.decode())
    if [r['source_name'] for r in rows]!=[prefix+n for n in names]:raise ValueError('caller theorem census drift')
    return rows


def checked_closure():
    order,pins=m.profile.closure(ROOT,[CHECKED_TARGET],{})
    if HELD in order:raise ValueError('held Premises dependency refused')
    return order,pins


def module_root(output, source):
    return output/'staged' if source.is_relative_to(output/'staged') else output


def identity_probe():
    pairs=[('Solidity.Backend.InternalFlow.RuntimeFrame.P1V2CallAgreement.source_outcomes',
            'Solidity.Backend.InternalFlow.RuntimeFrameP1V2CallAgreement'),
           ('Solidity.Backend.InternalFlow.RuntimeFrame.NoneProducer.returns',
            'Solidity.Backend.InternalFlow.RuntimeFrameNoneProducer'),
           ('Solidity.Backend.InternalFlow.RuntimeFrame.P1V2CallAgreementControls.target_success',
            'Solidity.Backend.InternalFlow.RuntimeFrameP1V2CallAgreementControls'),
           (PREFIX+'run_code','ExecutionCall'),(CHECKED_PREFIX+'compiled_native','CheckedExecutionCall')]
    body='import Lean\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n'
    for name,expected in pairs:
        body+=('  let some index := env.getModuleIdxFor? `'+name+' | throwError "missing module identity"\n'
               '  let actual := env.header.moduleNames[index.toNat]!\n'
               '  unless actual == `'+expected+' do throwError "wrong canonical module {actual}"\n'
               '  logInfo "MODULE_IDENTITY_PASS '+name+' '+expected+'"\n')
    return pairs,body


def captured_log(path):
    payload=path.read_bytes()
    return hashlib.sha256(payload).hexdigest(),payload.decode()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checked',action='store_true')
    parser.add_argument('--parent',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();parent=args.parent.resolve();parent_file=parent/'receipt.json'
    receipt=read_parent(parent_file);verify_parent(parent,receipt)
    raw=(ROOT/SOURCE).read_bytes();rows=inventory(raw);pin=hashlib.sha256(raw).hexdigest()
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False);library=out/'library';library.mkdir()
    protected={str(p):m.check.sha(p) for p in [Path(__file__).resolve(),helper]}
    m.joint.original.pin_authenticated_file(protected,parent_file,PARENT_SHA)
    env=m.profile.isolated_environment(os.environ,library);env['LEAN_PATH']=str(library)+':'+str(parent/'library')
    sdk=subprocess.check_output([str(m.check.LEAN),'--print-prefix'],env=env,text=True).strip()
    if sdk!=receipt['sdk_root']:raise ValueError('caller SDK mismatch')
    steps=[]
    def run(tag,source,artifact=None):
        command=[str(m.check.LEAN),'-j1','--tstack=131072','--root='+str(module_root(out,source))]
        # TermSize's asynchronous tasks exhaust virtual thread stacks at the fixed cap.
        # Keep other modules' existing elaboration scheduling and heartbeat accounting.
        if source.name=='TermSize.lean':command+=['-DElab.async=false']
        if artifact:command+=['-o',str(artifact)]
        command.append(str(source));log=out/(tag+'.log')
        with log.open('w') as stream:done=subprocess.run(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        digest,text=captured_log(log)
        steps.append({'command':command,'exit':done.returncode,'log':str(log),'sha256':digest})
        if done.returncode:raise SystemExit('EXECUTION_CALL_FAIL '+str(log))
        return text
    extra_order=[];extra_pins={};extra_artifacts={};reused={}
    if args.checked:
        extra_order,extra_pins=checked_closure()
        for relative,parent_record in receipt['artifacts'].items():
            module=relative[:-5] if relative!=m.SOURCE else 'ExecutionReplies'
            m.joint.copy_parent_object(parent/'library'/(module+'.olean'),library/(module+'.olean'),
                parent_record['artifact_sha256'],protected)
            reused[relative]=parent_record['artifact_sha256']
        for relative in extra_order:
            source_pin=extra_pins[relative]['source_sha256']
            if relative in receipt['source_pins']:
                if receipt['source_pins'][relative]!=extra_pins[relative]:raise ValueError('checked common source drift')
                continue
            source=out/'staged'/relative;artifact=library/(relative[:-5]+'.olean')
            artifact.parent.mkdir(parents=True,exist_ok=True)
            record=m.check.compile_staged(ROOT/relative,source,artifact,
                lambda src,obj:run(relative[:-5].replace('/','_'),src,obj))
            if record['source_sha256']!=source_pin:raise ValueError('checked dependency source drift')
            protected.update({str(ROOT/relative):source_pin,str(source):source_pin,str(artifact):record['artifact_sha256']})
            extra_artifacts[relative]=record
    staged=out/'ExecutionCall.lean';artifact=library/'ExecutionCall.olean'
    record=m.check.compile_staged(ROOT/SOURCE,staged,artifact,lambda src,obj:run('caller',src,obj))
    if record['source_sha256']!=pin:raise ValueError('caller source changed before compile')
    protected.update({str(ROOT/SOURCE):pin,str(staged):pin,str(artifact):record['artifact_sha256']})
    probe=out/'Probe.lean';probe.write_text('import ExecutionCall\n'+''.join('#print axioms '+PREFIX+n+'\n' for n in NAMES))
    protected[str(probe)]=m.check.sha(probe);axioms=m.joint.parse_axioms(run('probe',probe),PREFIX,NAMES)
    checked_record=None;checked_axioms={};checked_rows=[]
    if args.checked:
        checked_raw=(ROOT/CHECKED_SOURCE).read_bytes();checked_rows=inventory(checked_raw,True)
        checked_pin=hashlib.sha256(checked_raw).hexdigest()
        checked_source=out/'CheckedExecutionCall.lean';checked_artifact=library/'CheckedExecutionCall.olean'
        checked_record=m.check.compile_staged(ROOT/CHECKED_SOURCE,checked_source,checked_artifact,
            lambda src,obj:run('checked',src,obj))
        if checked_record['source_sha256']!=checked_pin:raise ValueError('checked caller source drift')
        protected.update({str(ROOT/CHECKED_SOURCE):checked_pin,str(checked_source):checked_pin,
                          str(checked_artifact):checked_record['artifact_sha256']})
        checked_probe=out/'CheckedProbe.lean'
        identity_pairs,identity_source=identity_probe()
        checked_probe.write_text('import CheckedExecutionCall\n'+identity_source+''.join('#print axioms '+CHECKED_PREFIX+n+'\n' for n in CHECKED_NAMES))
        protected[str(checked_probe)]=m.check.sha(checked_probe)
        checked_log=run('checked_probe',checked_probe)
        checked_axioms=m.joint.parse_axioms(checked_log,CHECKED_PREFIX,CHECKED_NAMES)
        if checked_log.count('MODULE_IDENTITY_PASS ')!=len(identity_pairs):raise ValueError('missing module identity controls')
        if checked_closure()!=(extra_order,extra_pins):
            raise ValueError('checked caller closure drift')
    verify_parent(parent,receipt)
    m.check.verify_hashes(protected|{s['log']:s['sha256'] for s in steps})
    if subprocess.check_output([str(m.check.LEAN),'--print-prefix'],env=env,text=True).strip()!=sdk:
        raise ValueError('caller SDK changed')
    result={'boundary':__doc__,'parent_receipt_sha256':PARENT_SHA,'parent':str(parent),
        'source':SOURCE,'fixture':record,'theorems':rows,'axioms':axioms,'steps':steps,
        'protected_sha256':protected,'parent_objects_verified':len(receipt['artifacts']),
        'sdk_root':sdk,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        'checked_mode':args.checked,'checked_source':CHECKED_SOURCE if args.checked else None,
        'checked_fixture':checked_record,'checked_theorems':checked_rows,'checked_axioms':checked_axioms,
        'module_identity_controls':identity_pairs if args.checked else [],'extra_order':extra_order,'extra_source_pins':extra_pins,'extra_artifacts':extra_artifacts,
        'reused_objects':reused,'original_obligations_discharged':0,'full_ro_adequacy':False,'runtime_gate_pass':False}
    (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print('EXECUTION_CALL_PASS parent_objects='+str(len(receipt['artifacts']))+' theorems='+str(len(axioms)+len(checked_axioms))+' fresh_dependencies='+str(len(extra_artifacts))+
          ' original_obligations_discharged=0 full_ro_adequacy=false')


if __name__=='__main__':main()
