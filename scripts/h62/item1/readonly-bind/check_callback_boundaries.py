#!/usr/bin/env python3
"""Guard callback boundary checks reusing substituted source/dependency artifacts.

Reuse only the exact saved, previously executed fresh-closure receipt pinned
below; verify every current project source and parent object before and after.
This is explicit checked-artifact reuse, not a fresh dependency rebuild, SDK
source certification, arbitrary receipt authentication or whole-goal acceptance.
Run under the existing bounded runner for exclusive lock and resource limits.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('callback_parent_profile', HERE/'check_capture_fixtures.py')
profile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile)
check = profile.check
PARENT_SHA = '6cc6b35a60ec17a7082721c467f086f3c3cd0114b75405e6f36eec2a69f26bee'
SOURCE = 'tests/h62/item1/readonly-bind/CallbackBoundaryControls.lean'
PREFIX = 'Solidity.H62.ReadonlyBind.CallbackBoundaryControls.'
NAMES = ['depth_inputs','static_inputs','depth_refusal_continues','static_refusal_continues',
         'admitted_inputs','admitted_credit_failure','observed_events','refusal_keeps_balance']


def read_parent(path):
    raw = path.read_bytes()
    if check.hashlib.sha256(raw).hexdigest() != PARENT_SHA:
        raise ValueError('unadmitted parent receipt bytes')
    return json.loads(raw)


def verify_objects(root, parent, receipt):
    for relative, pin in receipt['source_pins'].items():
        if check.sha(root/relative) != pin['source_sha256']:
            raise ValueError('parent current source drift: '+relative)
        module = relative[:-5] if relative not in profile.EXTRAS else profile.EXTRAS[relative]
        if check.sha(parent/'library'/(module+'.olean')) != receipt['artifacts'][relative]['artifact_sha256']:
            raise ValueError('parent object substitution: '+relative)


def parse_axioms(log):
    records = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", log)
    if len(records) != len(NAMES) or {n for n, _ in records} != {PREFIX+n for n in NAMES}:
        raise ValueError('missing or duplicate callback axiom records')
    result = {n: [a.strip() for a in raw.split(',') if a.strip()] for n, raw in records}
    if any(set(a)-check.ALLOWED for a in result.values()):
        raise ValueError('unexpected callback axiom')
    return result


def observed_counts(axioms, receipt):
    return {'joint_inputs':sum(PREFIX+n in axioms for n in NAMES if n.endswith('_inputs')),
            'theorems':len(axioms),'parent_objects':len(receipt['artifacts'])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--parent', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    parent = args.parent.resolve()
    receipt_path = parent/'receipt.json'
    receipt = read_parent(receipt_path)
    order, pins = profile.closure(ROOT, profile.TARGETS, profile.EXTRAS)
    if order != receipt['project_order'] or pins != receipt['source_pins']:
        raise ValueError('parent import graph/current source drift')
    verify_objects(ROOT, parent, receipt)
    check.verify_hashes(receipt['input_pins'])
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    library = out/'library'
    library.mkdir()
    env = profile.isolated_environment(os.environ, library)
    env['LEAN_PATH'] = str(library)+':'+str(parent/'library')
    sdk = subprocess.check_output([str(check.LEAN),'--print-prefix'],env=env,text=True).strip()
    if str(Path(sdk).resolve()) != receipt['sdk_root']:
        raise ValueError('SDK root differs from parent')
    if profile.imports((ROOT/SOURCE).read_text()) != ['Solidity.Lowering.Readonly.EnvironmentCreditControls']:
        raise ValueError('unadmitted boundary control imports')
    protected = {str(p): check.sha(p) for p in [Path(__file__).resolve(),receipt_path]}
    source_pin = check.sha(ROOT/SOURCE)
    steps = []
    def run(tag, source, artifact=None):
        command = [str(check.LEAN),'-j1','--tstack=131072','--root='+str(out)]
        if artifact:
            command += ['-o',str(artifact)]
        command.append(str(source))
        log = out/(tag+'.log')
        with log.open('w') as stream:
            done = subprocess.run(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        raw = log.read_bytes()
        steps.append({'command':command,'exit':done.returncode,'log':str(log),
                      'sha256':check.hashlib.sha256(raw).hexdigest()})
        if done.returncode:
            raise SystemExit('CALLBACK_BOUNDARIES_FAIL '+str(log))
        return raw.decode()
    source, artifact = out/'CallbackBoundaryControls.lean', library/'CallbackBoundaryControls.olean'
    new = check.compile_staged(ROOT/SOURCE,source,artifact,lambda staged,obj:run('fixture',staged,obj))
    if new['source_sha256'] != source_pin:
        raise ValueError('callback source drift before compile')
    protected.update({str(source):source_pin,str(artifact):new['artifact_sha256']})
    probe = out/'Probe.lean'
    probe.write_text('import CallbackBoundaryControls\n'+''.join('#print axioms '+PREFIX+n+'\n' for n in NAMES))
    protected[str(probe)] = check.sha(probe)
    axioms = parse_axioms(run('axioms',probe))
    verify_objects(ROOT,parent,receipt)
    check.verify_hashes(receipt['input_pins'] | protected | {s['log']:s['sha256'] for s in steps})
    if check.sha(ROOT/SOURCE) != source_pin:
        raise ValueError('callback current source drift')
    if subprocess.check_output([str(check.LEAN),'--print-prefix'],env=env,text=True).strip() != sdk:
        raise ValueError('SDK root changed')
    result = {'boundary':__doc__,'parent_receipt_sha256':PARENT_SHA,'parent':str(parent),
              'reused_project_modules':len(order),'parent_objects_checked':len(receipt['artifacts']),
              'source':SOURCE,'fixture':new,'steps':steps,'axioms':axioms,
              'protected_sha256':protected,'sdk_root':sdk,
              'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
              'full_goal_acceptance':False}
    (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    counts=observed_counts(axioms,receipt)
    print('CALLBACK_BOUNDARIES_PASS '+' '.join(k+'='+str(v) for k,v in counts.items()))


if __name__=='__main__':main()
