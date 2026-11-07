#!/usr/bin/env python3
"""Guard source-named or stale-oracle evidence replacing native call execution.

Build the exact unheld SourceCallBytes/MachineV2 closure and the additive target
adapter in a private library, without project-cache fallback. No Source/Core or
whole-world adequacy is inferred. SDK remains an explicit trusted tool input.
Use the existing bounded runner for serial resource limits and writer lock.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[4]
helper=ROOT/'scripts/h62/item1/readonly-bind/check_credit_joints.py'
spec=importlib.util.spec_from_file_location('execution_joint_helper',helper)
joint=importlib.util.module_from_spec(spec);spec.loader.exec_module(joint)
profile,check=joint.profile,joint.check
TARGET='Solidity.Backend.Passes.SourceCallBytes'
SOURCE='tests/h62/item2/audit-readonly-calls/ExecutionReplies.lean'
PREFIX='Solidity.H62.ReadonlyCalls.ExecutionReplies.'
NAMES=['prepare_input','prepare_context','configured_reply','configured_accepts','callIn_frame',
       'execution_transport','echo_success','echo_revert','fault_refused','pending_refused','not_always_revert']


def theorem_inventory(raw):
    if profile.imports(raw.decode())!=[TARGET]:raise ValueError('unadmitted execution adapter imports')
    rows=joint.export.census.declarations_text(SOURCE,raw.decode())
    names=[r['source_name'] for r in rows]
    if names!=[PREFIX+n for n in NAMES]:raise ValueError('execution theorem census drift')
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False);library=out/'library';library.mkdir()
    order,pins=profile.closure(ROOT,[TARGET],{})
    raw=(ROOT/SOURCE).read_bytes();rows=theorem_inventory(raw);source_pin=check.hashlib.sha256(raw).hexdigest()
    protected={str(p):check.sha(p) for p in [Path(__file__).resolve(),helper,
        ROOT/'scripts/h62/item1/readonly-bind/check_original_callback.py',
        ROOT/'scripts/h62/item1/readonly-bind/check_callback_boundaries.py',
        ROOT/'scripts/h62/item1/readonly-bind/check_capture_fixtures.py',
        ROOT/'scripts/h62/item1/readonly-bind/check_encoding_fixture.py',
        ROOT/'scripts/h62/item1/readonly-bind/case_ledger.py',
        ROOT/'scripts/h62/item1/readonly-bind/overlay.py',
        ROOT/'scripts/h62/item2/audit-readonly-calls/census.py',
        ROOT/'scripts/h62/item2/audit-readonly-calls/export_signatures.py',check.LEAN,ROOT/'lean-toolchain']}
    env=profile.isolated_environment(os.environ,library)
    sdk=subprocess.check_output([str(check.LEAN),'--print-prefix'],env=env,text=True).strip()
    if Path(sdk).resolve()!=check.LEAN.resolve().parent.parent:raise ValueError('execution SDK mismatch')
    steps=[];artifacts={}
    def run(tag,source,artifact=None):
        command=[str(check.LEAN),'-j1','--tstack=131072','--root='+str(out/'staged')]
        if artifact:
            artifact.parent.mkdir(parents=True,exist_ok=True);command+=['-o',str(artifact)]
        command.append(str(source));log=out/(tag+'.log')
        with log.open('w') as stream:done=subprocess.run(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        payload=log.read_bytes();steps.append({'command':command,'exit':done.returncode,'log':str(log),
            'sha256':check.hashlib.sha256(payload).hexdigest()})
        if done.returncode:raise SystemExit('EXECUTION_REPLIES_FAIL '+str(log))
        return payload.decode()
    for relative in order+[SOURCE]:
        module=relative[:-5] if relative!=SOURCE else 'ExecutionReplies'
        staged=out/'staged'/(module+'.lean');artifact=library/(module+'.olean')
        expected=pins[relative]['source_sha256'] if relative!=SOURCE else source_pin
        record=check.compile_staged(ROOT/relative,staged,artifact,
            lambda src,obj:run(module.replace('/','_'),src,obj))
        if record['source_sha256']!=expected:raise ValueError('execution source changed before compile')
        artifacts[relative]=record
        protected.update({str(ROOT/relative):expected,str(staged):expected,str(artifact):record['artifact_sha256']})
    probe=out/'staged/Probe.lean';probe.write_text('import ExecutionReplies\n'+
        ''.join('#print axioms '+PREFIX+n+'\n' for n in NAMES))
    protected[str(probe)]=check.sha(probe)
    axioms=joint.parse_axioms(run('probe',probe),PREFIX,NAMES)
    if profile.closure(ROOT,[TARGET],{})!=(order,pins):raise ValueError('execution closure changed')
    check.verify_hashes(protected|{step['log']:step['sha256'] for step in steps})
    if subprocess.check_output([str(check.LEAN),'--print-prefix'],env=env,text=True).strip()!=sdk:
        raise ValueError('execution SDK changed')
    receipt={'boundary':__doc__,'target':TARGET,'source':SOURCE,'source_pins':pins,'project_order':order,
        'artifacts':artifacts,'theorems':rows,'axioms':axioms,'steps':steps,'protected_sha256':protected,
        'sdk_root':sdk,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        'original_obligations_discharged':0,'full_ro_adequacy':False,'runtime_gate_pass':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('EXECUTION_REPLIES_PASS project_modules='+str(len(order))+' theorems='+str(len(axioms))+
          ' original_obligations_discharged=0 full_ro_adequacy=false')


if __name__=='__main__':main()
