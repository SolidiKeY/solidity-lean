#!/usr/bin/env python3
"""Guard current dependency semantics being substituted for frozen joint witnesses.

Compile the exact assigned Git base's unheld callback closure in isolation,
then the additive witness unchanged. No old/current timing comparison, cache
fallback, statement repair or whole-goal acceptance. SDK remains toolchain input.
Run under the audit bounded runner for writer lock, serialism and memory limits.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('original_callback_helper',HERE/'check_callback_boundaries.py')
callback = importlib.util.module_from_spec(spec);spec.loader.exec_module(callback)
profile, check = callback.profile, callback.check
export = profile.load('original_callback_export',ROOT/'scripts/h62/item2/audit-readonly-calls/export_signatures.py')
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
FROZEN_SHA = 'e07aa0fe5f1a94c292c6d9edc22eee478f45c560b1802fab5e7ac581da9a2ffb'
TARGET = 'Solidity.Lowering.Readonly.EnvironmentCreditControls'
INTERFACES = ['Solidity.Lowering.Readonly.EnvironmentSteps.refused',
              'Solidity.Lowering.Readonly.EnvironmentCredit.callback_credit_failed']


def read_git(relative):
    return subprocess.check_output(['git','show',BASE+':'+relative],cwd=ROOT)


def snapshot(read, target, destination):
    seen, active, order, pins = set(), set(), [], {}
    def walk(module):
        if module == profile.HELD:
            raise ValueError('historically held workload refused')
        if module in active:
            raise ValueError('cyclic frozen import')
        if module in seen:
            return
        if not module.startswith('Solidity.'):
            if module.split('.')[0] not in {'Lean','Init','Std'}:
                raise ValueError('foreign frozen dependency')
            return
        active.add(module)
        relative = module.replace('.','/')+'.lean'
        raw = read(relative)
        deps = profile.imports(raw.decode())
        for dep in deps:
            walk(dep)
        target_path = destination/relative
        target_path.parent.mkdir(parents=True,exist_ok=True)
        target_path.write_bytes(raw);target_path.chmod(0o444)
        pins[relative] = {'source_sha256':check.hashlib.sha256(raw).hexdigest(),'imports':deps}
        active.remove(module);seen.add(module);order.append(relative)
    walk(target)
    return order,pins


def select_interfaces(raw, originals):
    if check.hashlib.sha256(raw).hexdigest() != FROZEN_SHA:
        raise ValueError('original792 artifact substitution')
    data = json.loads(raw)
    if data['base'] != BASE or data['theorem_count'] != 792 or len(data['declarations']) != 792:
        raise ValueError('original792 membership drift')
    keys = [(r['file'],r['source_name']) for r in data['declarations']]
    if len(set(keys)) != 792:
        raise ValueError('duplicate original identity')
    rows = []
    for name in INTERFACES:
        found = [r for r in data['declarations'] if r['source_name']==name]
        if len(found) != 1:
            raise ValueError('missing original callback interface')
        row = found[0]
        actual = [r for r in export.census.declarations_text(row['file'],originals[row['file']].decode())
                  if r['source_name']==name]
        if len(actual) != 1 or any(actual[0][k]!=row[k] for k in ['signature_sha256','variable_context','visibility']):
            raise ValueError('original callback source statement drift')
        rows.append(row)
    return {'base':BASE,'modules':[{'file':p} for p in sorted({r['file'] for r in rows})],
            'declarations':rows}


def pin_authenticated_file(protected, path, digest):
    """Retain the authenticated buffer digest; never adopt a later file read."""
    protected[str(path)] = digest
    check.verify_hashes({str(path):digest})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--frozen',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    if subprocess.check_output(['git','rev-parse',BASE+'^{commit}'],cwd=ROOT,text=True).strip()!=BASE:
        raise ValueError('original base identity mismatch')
    subprocess.run(['git','merge-base','--is-ancestor',BASE,'HEAD'],cwd=ROOT,check=True)
    frozen_toolchain = read_git('lean-toolchain')
    if frozen_toolchain != (ROOT/'lean-toolchain').read_bytes():
        raise ValueError('frozen/live toolchain differ; no independent toolchain choice')
    out = args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    original = out/'original'
    order,pins = snapshot(read_git,TARGET,original)
    inventory = select_interfaces(args.frozen.read_bytes(),{p:(original/p).read_bytes() for p in order})
    (out/'inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
    library = out/'library';library.mkdir()
    env = profile.isolated_environment(os.environ,library)
    sdk = subprocess.check_output([str(check.LEAN),'--print-prefix'],env=env,text=True).strip()
    if Path(sdk).resolve()!=check.LEAN.resolve().parent.parent:
        raise ValueError('frozen gate SDK root mismatch')
    protected = {str(p):check.sha(p) for p in [Path(__file__).resolve(),HERE/'check_callback_boundaries.py',
        HERE/'check_capture_fixtures.py',HERE/'check_encoding_fixture.py',HERE/'case_ledger.py',
        HERE/'overlay.py',ROOT/'scripts/h62/item2/audit-readonly-calls/census.py',
        ROOT/'scripts/h62/item2/audit-readonly-calls/export_signatures.py',
        check.LEAN]}
    pin_authenticated_file(protected,args.frozen,FROZEN_SHA)
    pin_authenticated_file(protected,ROOT/'lean-toolchain',check.hashlib.sha256(frozen_toolchain).hexdigest())
    protected[str(out/'inventory.json')] = check.sha(out/'inventory.json')
    steps, artifacts = [], {}
    def run(tag, source, artifact=None):
        command = [str(check.LEAN),'-j1','--tstack=131072','--root='+str(out/'staged')]
        if artifact:
            artifact.parent.mkdir(parents=True,exist_ok=True)
            command += ['-o',str(artifact)]
        command.append(str(source))
        log = out/(tag+'.log')
        with log.open('w') as stream:
            done = subprocess.run(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        raw = log.read_bytes()
        steps.append({'command':command,'exit':done.returncode,'log':str(log),
                      'sha256':check.hashlib.sha256(raw).hexdigest()})
        if done.returncode:
            raise SystemExit('ORIGINAL_CALLBACK_FAIL '+str(log))
        return raw.decode()
    for relative in order+[callback.SOURCE]:
        source = original/relative if relative in pins else ROOT/relative
        module = relative[:-5] if relative in pins else 'CallbackBoundaryControls'
        staged, artifact = out/'staged'/(module+'.lean'), library/(module+'.olean')
        record = check.compile_staged(source,staged,artifact,lambda src,obj:run(module.replace('/','_'),src,obj))
        if relative in pins and record['source_sha256']!=pins[relative]['source_sha256']:
            raise ValueError('frozen source changed after Git snapshot')
        protected.update({str(source):record['source_sha256'],str(staged):record['source_sha256'],
                          str(artifact):record['artifact_sha256']})
        artifacts[relative] = record
    probe = out/'staged/Probe.lean'
    probe.write_text('import CallbackBoundaryControls\n'+export.generate(inventory)+
                     ''.join('#print axioms '+callback.PREFIX+n+'\n' for n in callback.NAMES))
    protected[str(probe)] = check.sha(probe)
    log = run('probe',probe)
    axioms = callback.parse_axioms(log)
    types = export.collect(log,inventory)
    (out/'types.json').write_text(json.dumps(types,indent=2)+'\n')
    for relative,pin in pins.items():
        if check.hashlib.sha256(read_git(relative)).hexdigest()!=pin['source_sha256']:
            raise ValueError('Git frozen source drift')
    check.verify_hashes(protected | {s['log']:s['sha256'] for s in steps})
    if subprocess.check_output([str(check.LEAN),'--print-prefix'],env=env,text=True).strip()!=sdk:
        raise ValueError('frozen gate SDK root changed')
    receipt = {'boundary':__doc__,'base':BASE,'project_order':order,'source_pins':pins,
               'artifacts':artifacts,'steps':steps,'axioms':axioms,'types_sha256':check.sha(out/'types.json'),
               'protected_sha256':protected,'sdk_root':sdk,'original792_count':792,
               'joint_interface_names':INTERFACES,'new_witness_theorems':8,
               'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
               'full_goal_acceptance':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('ORIGINAL_CALLBACK_PASS base='+BASE+' project_modules='+str(len(order))+' interfaces=2 joint_inputs=3')


if __name__=='__main__':main()
