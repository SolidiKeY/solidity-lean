#!/usr/bin/env python3
"""Guard credit feasibility claims from unbound parents or partial hypotheses.

Admit only two actual saved parent executions: exact frozen C6 and checked
current source. Verify reused sources/objects before and after the new proof.
Artifact reuse is not a fresh dependency rebuild or SDK source certification;
only three selected original interfaces are covered, not the full goal.
Run under the existing serial bounded runner and writer lock.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[4]
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('credit_original_helper',HERE/'check_original_callback.py')
original=importlib.util.module_from_spec(spec);spec.loader.exec_module(original)
profile,check,export=original.profile,original.check,original.export
PARENTS={'frozen':'49e5b4c46b5259c8b1b164d71378238731472973aabd3650a26b10900a52baa0',
         'current':'6cc6b35a60ec17a7082721c467f086f3c3cd0114b75405e6f36eec2a69f26bee'}
SOURCE='tests/h62/item1/readonly-bind/CreditJointControls.lean'
PREFIX='Solidity.H62.ReadonlyBind.CreditJointControls.'
NAMES=['known_inputs','unknown_inputs','failed_inputs','known_success','unknown_success',
       'credit_failure','known_balance_and_storage','unknown_no_credit']
INTERFACES=['Solidity.Lowering.Readonly.EnvironmentCredit.'+n for n in ['known','unknown','failed']]


def read_parent(path,mode):
    raw=path.read_bytes()
    if mode not in PARENTS or check.hashlib.sha256(raw).hexdigest()!=PARENTS[mode]:
        raise ValueError('unadmitted credit parent receipt')
    return json.loads(raw)


def verify_parent(parent,receipt,mode):
    if mode=='frozen':
        if receipt['base']!=original.BASE:raise ValueError('wrong frozen base')
        for relative,pin in receipt['source_pins'].items():
            raw=original.read_git(relative)
            if check.hashlib.sha256(raw).hexdigest()!=pin['source_sha256']:
                raise ValueError('frozen Git source drift')
            if check.sha(parent/'original'/relative)!=pin['source_sha256']:
                raise ValueError('frozen source snapshot substitution')
    else:
        order,pins=profile.closure(ROOT,profile.TARGETS,profile.EXTRAS)
        if order!=receipt['project_order'] or pins!=receipt['source_pins']:
            raise ValueError('current parent source/import drift')
        check.verify_hashes(receipt['input_pins'])
    for relative,record in receipt['artifacts'].items():
        if mode=='frozen':
            module=relative[:-5] if relative in receipt['source_pins'] else 'CallbackBoundaryControls'
        else:module=relative[:-5] if relative not in profile.EXTRAS else profile.EXTRAS[relative]
        if check.sha(parent/'library'/(module+'.olean'))!=record['artifact_sha256']:
            raise ValueError('credit parent object substitution')
    for step in receipt['steps']:
        if check.sha(Path(step['log']))!=step['sha256']:
            raise ValueError('credit parent log substitution')
    # SDK is an explicit trusted toolchain input, never inferred from project cache.
    pins=receipt['protected_sha256'] if mode=='frozen' else receipt['input_pins']
    check.verify_hashes({str(p):pins[str(p)] for p in [check.LEAN,ROOT/'lean-toolchain']})


def inventory(raw):
    if check.hashlib.sha256(raw).hexdigest()!=original.FROZEN_SHA:
        raise ValueError('frozen792 artifact substitution')
    data=json.loads(raw)
    if data['base']!=original.BASE or len(data['declarations'])!=792:
        raise ValueError('original792 membership drift')
    rows=[]
    for name in INTERFACES:
        found=[r for r in data['declarations'] if r['source_name']==name]
        if len(found)!=1:raise ValueError('missing original credit interface')
        row=found[0]
        parsed=[r for r in export.census.declarations_text(row['file'],original.read_git(row['file']).decode())
                if r['source_name']==name]
        if len(parsed)!=1 or any(parsed[0][k]!=row[k] for k in ['signature_sha256','variable_context','visibility']):
            raise ValueError('original credit statement drift')
        rows.append(row)
    return {'base':original.BASE,'modules':[{'file':rows[0]['file']}],'declarations':rows}


def parse_axioms(log):
    records=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",log)
    if len(records)!=len(NAMES) or {n for n,_ in records}!={PREFIX+n for n in NAMES}:
        raise ValueError('missing or duplicate credit axiom records')
    result={n:[a.strip() for a in raw.split(',') if a.strip()] for n,raw in records}
    if any(set(a)-check.ALLOWED for a in result.values()):raise ValueError('unexpected credit axiom')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',choices=list(PARENTS),required=True)
    parser.add_argument('--parent',type=Path,required=True)
    parser.add_argument('--frozen',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();parent=args.parent.resolve();parent_file=parent/'receipt.json'
    receipt=read_parent(parent_file,args.profile);verify_parent(parent,receipt,args.profile)
    inv=inventory(args.frozen.read_bytes())
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False);library=out/'library';library.mkdir()
    protected={str(p):check.sha(p) for p in [Path(__file__).resolve(),HERE/'check_original_callback.py',
        HERE/'check_callback_boundaries.py',HERE/'check_capture_fixtures.py',HERE/'check_encoding_fixture.py',
        ROOT/'scripts/h62/item2/audit-readonly-calls/census.py',
        ROOT/'scripts/h62/item2/audit-readonly-calls/export_signatures.py']}
    original.pin_authenticated_file(protected,parent_file,PARENTS[args.profile])
    original.pin_authenticated_file(protected,args.frozen,original.FROZEN_SHA)
    env=profile.isolated_environment(os.environ,library)
    env['LEAN_PATH']=str(library)+':'+str(parent/'library')
    sdk=subprocess.check_output([str(check.LEAN),'--print-prefix'],env=env,text=True).strip()
    if str(Path(sdk).resolve())!=str(Path(receipt['sdk_root']).resolve()):raise ValueError('credit SDK root mismatch')
    raw=(ROOT/SOURCE).read_bytes();source_pin=check.hashlib.sha256(raw).hexdigest()
    if profile.imports(raw.decode())!=['Solidity.Lowering.Readonly.EnvironmentCreditControls']:
        raise ValueError('unadmitted credit imports')
    steps=[]
    def run(tag,source,artifact=None):
        command=[str(check.LEAN),'-j1','--tstack=131072','--root='+str(out)]
        if artifact:command+=['-o',str(artifact)]
        command.append(str(source));log=out/(tag+'.log')
        with log.open('w') as stream:
            done=subprocess.run(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        rawlog=log.read_bytes();steps.append({'command':command,'exit':done.returncode,'log':str(log),
            'sha256':check.hashlib.sha256(rawlog).hexdigest()})
        if done.returncode:raise SystemExit('CREDIT_JOINTS_FAIL '+str(log))
        return rawlog.decode()
    source,artifact=out/'CreditJointControls.lean',library/'CreditJointControls.olean'
    record=check.compile_staged(ROOT/SOURCE,source,artifact,lambda src,obj:run('fixture',src,obj))
    if record['source_sha256']!=source_pin:raise ValueError('credit source changed before compile')
    protected.update({str(source):source_pin,str(artifact):record['artifact_sha256']})
    probe=out/'Probe.lean'
    probe.write_text('import CreditJointControls\n'+export.generate(inv)+
                     ''.join('#print axioms '+PREFIX+n+'\n' for n in NAMES))
    protected[str(probe)]=check.sha(probe);log=run('probe',probe)
    axioms=parse_axioms(log);types=export.collect(log,inv)
    payload=json.dumps(types,indent=2)+'\n';(out/'types.json').write_text(payload)
    protected[str(out/'types.json')]=check.hashlib.sha256(payload.encode()).hexdigest()
    verify_parent(parent,receipt,args.profile)
    check.verify_hashes(protected|{s['log']:s['sha256'] for s in steps})
    if check.sha(ROOT/SOURCE)!=source_pin:raise ValueError('credit current source drift')
    if subprocess.check_output([str(check.LEAN),'--print-prefix'],env=env,text=True).strip()!=sdk:
        raise ValueError('credit SDK root changed')
    result={'boundary':__doc__,'profile':args.profile,'parent_receipt_sha256':PARENTS[args.profile],
            'parent':str(parent),'parent_objects_verified':len(receipt['artifacts']),
            'source':SOURCE,'fixture':record,'steps':steps,'axioms':axioms,'types_sha256':protected[str(out/'types.json')],
            'protected_sha256':protected,'sdk_root':sdk,'joint_interface_names':INTERFACES,
            'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
            'full_goal_acceptance':False}
    (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print('CREDIT_JOINTS_PASS profile='+args.profile+' interfaces='+str(len(types['declarations']))+
          ' proof_theorems='+str(len(axioms))+' parent_objects='+str(len(receipt['artifacts'])))


if __name__=='__main__':main()
