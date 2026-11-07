#!/usr/bin/env python3
"""Guard primitive-transport credit from unadmitted receipts or dropped original rows.

Only the exact executed frozen/current pair below is admitted. Coverage is joint
input satisfiability with original applications, not compiler/whole-model
adequacy, definition equivalence or runtime acceptance. Preserve all other rows.
"""
import argparse
from collections import Counter
import copy
import hashlib
import importlib.util
import json
import subprocess
from pathlib import Path

spec=importlib.util.spec_from_file_location('effect_proof_gate',Path(__file__).with_name('check_primitive_transport.py'))
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
COVERAGE_BASE='e6a0ec767f081273fab6ebce82a53f8775414bb0'
CANONICAL_SHA='85cfe70267b5d96585d9d344b2e381906f1f0f05bab6a8df50a09bb7cc559836'
COVERAGE_PATH='tests/h62/item2/audit-readonly-calls/coverage.json'
ADMITTED={'frozen':'4802c491d6e5bd616e8af86ecec8514da33480f573de1f04cc5dbe4e1ad57f48',
          'current':'16b93f2f1ca30d81538b405936413a69bb16271f68de5dc3f3cd025c10bc5d7b'}


def read_receipt(path,mode):
    return gate.current.original.load_pinned(path,ADMITTED[mode])


def verify_mode(path,mode):
    r=read_receipt(path,mode)
    if r['mode']!=mode or r['base']!=gate.original.BASE or r['source']!=gate.SOURCE:raise ValueError('wrong primitive receipt scope')
    wanted=gate.INTERFACES
    if r['interface_names']!=wanted or set(r['axioms'])!={gate.PREFIX+n for n in gate.NAMES}:raise ValueError('incomplete primitive receipt')
    if not r['steps'] or any(s['exit']!=0 for s in r['steps']):raise ValueError('failed proof step')
    gate.check.verify_hashes(r['protected_sha256']|{s['log']:s['sha256'] for s in r['steps']})
    source=(gate.ROOT/gate.SOURCE).read_bytes()
    if hashlib.sha256(source).hexdigest()!=r['source_sha256']:raise ValueError('witness source drift')
    gate.inventory(source)
    for relative,pin in r['source_pins'].items():
        raw=gate.original.read_git(relative) if mode=='frozen' else (gate.ROOT/relative).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=pin['source_sha256']:raise ValueError('source dependency drift')
    if mode=='current' and gate.profile.closure(gate.ROOT,[gate.TARGET],{})!=(r['project_order'],r['source_pins']):raise ValueError('current import graph drift')
    types=gate.current.original.load_pinned(path.parent/'types.json',r['types_sha256'])
    # Reparse actual sealed compiler output, not just copied metadata fields.
    step=r['steps'][-1];raw_log=Path(step['log']).read_bytes()
    if hashlib.sha256(raw_log).hexdigest()!=step['sha256']:raise ValueError('probe log drift')
    inventory={'base':r['base'],'modules':[{'file':gate.TARGET.replace('.','/')+'.lean'}],'declarations':r['interfaces']}
    if gate.original.export.collect(raw_log.decode(),inventory)!=types:raise ValueError('type/log mismatch')
    if gate.joint.parse_axioms(raw_log.decode(),gate.PREFIX,gate.NAMES)!=r['axioms']:raise ValueError('axiom/log mismatch')
    return r,types


def apply(frozen,coverage,pair,types):
    rows=copy.deepcopy(frozen);updated=copy.deepcopy(coverage)
    if rows['base']!=gate.original.BASE or len(rows['declarations'])!=792:raise ValueError('original792 mismatch')
    by={r['source_name']:r for r in rows['declarations']}
    if len(by)!=792:raise ValueError('duplicate original identity')
    if pair['frozen']['source_sha256']!=pair['current']['source_sha256']:raise ValueError('different primitive clients')
    for mode in ['frozen','current']:
        if pair[mode]['mode']!=mode:raise ValueError('receipt mode substitution')
        found={r['source_name']:r for r in types[mode]['declarations']}
        if len(found)!=len(types[mode]['declarations']) or len(found)!=8 or set(found)!=set(gate.INTERFACES):raise ValueError('type coverage mismatch')
        if any(found[name]['raw_type_sha256']!=by[name]['elaborated']['raw_type_sha256'] for name in found):raise ValueError('original kernel type mismatch')
    entries={r['source_name']:r for r in updated['entries']}
    if len(entries)!=len(updated['entries']):raise ValueError('duplicate coverage identity')
    for name,entry in entries.items():
        if name not in by or entry['status']!=by[name]['witness_status'] or entry['signature_sha256']!=by[name]['signature_sha256']:raise ValueError('reviewed coverage baseline drift')
    changes=[]
    for name,proof in zip(gate.INTERFACES,gate.NAMES[:8],strict=True):
        row=by[name]
        if row['witness_status']!='pending' or name in entries:raise ValueError('not a newly pending original case')
        entry={'source_name':name,'signature_sha256':row['signature_sha256'],'status':'joint-witness','proof':gate.PREFIX+proof,
               'global_premises':'No assumed global model or compiler record. Explicit empty contract/layout and nonempty typed locals. Injectivity applies to the SAME true/true pair and its equality premise.',
               'per_input':'Mixed bool/uint/int/bool locals true/9/-3/false, inhabited numeric bounds, last index and exact same source/target values; no ABI/compiler/profile implication.',
               'evidence':'primitive-transport/frozen-final/receipt.json and primitive-transport/current-final/receipt.json',
               'evidence_manifest':'tests/h62/item2/audit-readonly-calls/primitive-transport.sha256',
               'frozen_receipt_sha256':ADMITTED['frozen'],'current_receipt_sha256':ADMITTED['current'],
               'proof_boundary':'Joint premise satisfiability and applications only; no definition equivalence, compiler success or H121 adequacy.'}
        updated['entries'].append(entry);row['witness_status']='joint-witness';row['witness']=entry
        row['premise_assessment']='Explicit primitive/local inputs and original applications kernel-checked at exact C6 and current closures; no compiler/profile adequacy inferred.'
        changes.append({'source_name':name,'before':'pending','after':'joint-witness','proof':entry['proof']})
    return rows,updated,{'schema':1,'original_count':792,'changes':changes,'changed_entries':8,
                         'before_counts':dict(Counter(r['witness_status'] for r in frozen['declarations'])),
                         'after_counts':dict(Counter(r['witness_status'] for r in rows['declarations'])),
                         'definition_equivalence_proved':False,'runtime_gate_pass':False}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True);p.add_argument('--reviewed',type=Path,required=True);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    with gate.current.headers.binder.writer_lease():
        pair={};types={}
        for mode in ['frozen','current']:pair[mode],types[mode]=verify_mode(args.root/(mode+'-final')/'receipt.json',mode)
        frozen=gate.current.original.load_pinned(args.reviewed,CANONICAL_SHA)
        gate.current.verify_frozen(frozen)
        raw=subprocess.check_output(['git','show',COVERAGE_BASE+':'+COVERAGE_PATH],cwd=gate.ROOT)
        coverage=json.loads(raw,object_pairs_hook=gate.current.original.pairs)
        rows,updated,delta=apply(frozen,coverage,pair,types)
        if subprocess.check_output(['git','show',COVERAGE_BASE+':'+COVERAGE_PATH],cwd=gate.ROOT)!=raw:raise ValueError('coverage baseline drift')
        args.output.mkdir(parents=True,exist_ok=False)
        receipt={'schema':1,'status':'failed','admitted_receipts':ADMITTED,'coverage_baseline_commit':COVERAGE_BASE,'coverage_input_sha256':hashlib.sha256(raw).hexdigest(),'collector_sha256':gate.check.sha(Path(__file__))}
        (args.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        (args.output/'coverage-before.json').write_bytes(raw)
        for name,value in [('census-updated.json',rows),('coverage-updated.json',updated),('delta.json',delta)]:
            (args.output/name).write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')
        for mode in ['frozen','current']:verify_mode(args.root/(mode+'-final')/'receipt.json',mode)
        if subprocess.check_output(['git','show',COVERAGE_BASE+':'+COVERAGE_PATH],cwd=gate.ROOT)!=raw:raise ValueError('coverage baseline changed during output sealing')
        if gate.check.sha(Path(__file__))!=receipt['collector_sha256']:raise ValueError('collector source drift')
        receipt.update(status='pass',output_sha256={name:gate.check.sha(args.output/name) for name in ['coverage-before.json','census-updated.json','coverage-updated.json','delta.json']},before_pending=delta['before_counts']['pending'],after_pending=delta['after_counts']['pending'],changed_entries=len(delta['changes']),runtime_gate_pass=False)
        (args.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print('PRIMITIVE_COVERAGE_PASS '+json.dumps(delta))


if __name__=='__main__':main()
