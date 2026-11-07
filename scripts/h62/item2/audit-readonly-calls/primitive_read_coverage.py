#!/usr/bin/env python3
"""Guard primitive read credit against dropped original identities or unadmitted evidence.

The committed admission JSON names the exact executed pair, never scan for a
successful receipt. Full parent/tool/object/source/log verification is delegated
to the existing checker; only these eight original cases may gain credit.
"""
import argparse
from collections import Counter
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
spec=importlib.util.spec_from_file_location('read_coverage_gate',Path(__file__).with_name('check_primitive_reads.py'))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);gate=module.gate
spec=importlib.util.spec_from_file_location('read_coverage_verifier',Path(__file__).with_name('initialization_coverage.py'))
verifier=importlib.util.module_from_spec(spec);spec.loader.exec_module(verifier);verifier.gate=gate
CANONICAL_SHA='77dd8d2b6a7f771206458bbef38915f9f5269964b861a1a803d8dbd601ee862d'
COVERAGE='tests/h62/item2/audit-readonly-calls/coverage.json'
ADMISSION=gate.ROOT/'tests/h62/item2/audit-readonly-calls/primitive-reads-admitted.json'
BASELINE='c2ea2ff3af9f796ed6e0cf051c7b28affd6cba71'
CREDIT_PROOFS=None
ENTRY_DETAILS={}
CONFIGURATION_SOURCE=None

def apply(frozen,coverage,pair,types,pins):
    rows=copy.deepcopy(frozen);updated=copy.deepcopy(coverage)
    by={r['source_name']:r for r in rows['declarations']}
    if rows['base']!=gate.original.BASE or len(rows['declarations'])!=792 or len(by)!=792:raise ValueError('original792 identity mismatch')
    if pair['frozen']['source_sha256']!=pair['current']['source_sha256']:raise ValueError('joint client substitution')
    for mode in ['frozen','current']:
        if pair[mode]['mode']!=mode:raise ValueError('receipt mode substitution')
        found={r['source_name']:r for r in types[mode]['declarations']}
        if len(found)!=len(gate.INTERFACES) or len(types[mode]['declarations'])!=len(gate.INTERFACES) or set(found)!=set(gate.INTERFACES):raise ValueError('exact type membership mismatch')
        if any(found[n]['raw_type_sha256']!=by[n]['elaborated']['raw_type_sha256'] for n in found):raise ValueError('original kernel type mismatch')
    entries={r['source_name']:r for r in updated['entries']}
    if len(entries)!=len(updated['entries']):raise ValueError('duplicate existing coverage')
    for name,entry in entries.items():
        if name not in by or entry['status']!=by[name]['witness_status'] or entry['signature_sha256']!=by[name]['signature_sha256']:raise ValueError('coverage baseline drift')
    proofs=gate.NAMES[1:9] if CREDIT_PROOFS is None else CREDIT_PROOFS
    if len(proofs)!=len(gate.INTERFACES) or len(set(proofs))!=len(proofs) or any(p not in gate.NAMES for p in proofs):raise ValueError('invalid explicit proof mapping')
    if not set(ENTRY_DETAILS)<=set(['global_premises','per_input','evidence','evidence_manifest','proof_boundary']):raise ValueError('identity/status metadata override forbidden')
    changes=[]
    for name,proof in zip(gate.INTERFACES,proofs,strict=True):
        row=by[name]
        if row['witness_status']!='pending' or name in entries:raise ValueError('not a pending original identity')
        entry={'source_name':name,'signature_sha256':row['signature_sha256'],'status':'joint-witness','proof':gate.PREFIX+proof,
          'global_premises':'Same inhabited two-declaration Env and nonempty Fields structure; all declaration/type/persistence/nonconst proofs supplied together.',
          'per_input':'Same a=true/b=default-false Source store, two-field intrinsic store and nonempty Bool locals. Relation, read/lookup premises and original applications checked jointly.',
          'evidence':'primitive-reads/validated/frozen-accepted/receipt.json and primitive-reads/validated/current-accepted/receipt.json',
          'evidence_manifest':'tests/h62/item2/audit-readonly-calls/primitive-reads.sha256',
          'frozen_receipt_sha256':pins['frozen'],'current_receipt_sha256':pins['current'],
          'proof_boundary':'Joint premise satisfiability and primitive evaluator outcomes only; not compiler/Source body/call/native-frame adequacy.'}
        entry.update(ENTRY_DETAILS)
        updated['entries'].append(entry);row['witness_status']='joint-witness';row['witness']=entry
        row['premise_assessment']='Same nonempty field/store inputs and exact original applications checked on frozen/current dependencies.'
        changes.append({'source_name':name,'before':'pending','after':'joint-witness','proof':entry['proof']})
    return rows,updated,{'original_count':792,'changes':changes,'changed_entries':len(gate.INTERFACES),'before_counts':dict(Counter(r['witness_status'] for r in frozen['declarations'])),'after_counts':dict(Counter(r['witness_status'] for r in rows['declarations'])),'runtime_gate_pass':False,'definition_equivalence_proved':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True);p.add_argument('--reviewed',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    with gate.current.headers.binder.writer_lease():
        collector_pin=gate.check.sha(Path(__file__))
        configuration_pin=gate.check.sha(CONFIGURATION_SOURCE) if CONFIGURATION_SOURCE else None
        admitted_raw=ADMISSION.read_bytes();pin=gate.hashlib.sha256(admitted_raw).hexdigest()
        pins=json.loads(admitted_raw,object_pairs_hook=gate.current.original.pairs)
        if set(pins)!={'frozen','current'} or any(not isinstance(v,str) or len(v)!=64 for v in pins.values()):raise ValueError('incomplete explicit admission')
        verifier.ADMITTED=pins
        pair={};types={}
        for mode in pins:pair[mode],types[mode]=verifier.verify_mode(a.root/(mode+'-accepted')/'receipt.json',mode)
        frozen=gate.current.original.load_pinned(a.reviewed,CANONICAL_SHA);gate.current.verify_frozen(frozen)
        raw=subprocess.check_output(['git','show',BASELINE+':'+COVERAGE],cwd=gate.ROOT)
        rows,updated,delta=apply(frozen,json.loads(raw),pair,types,pins)
        a.output.mkdir(parents=True,exist_ok=False)
        for name,value in [('census-updated.json',rows),('coverage-updated.json',updated),('delta.json',delta)]:
            (a.output/name).write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')
        for mode in pins:verifier.verify_mode(a.root/(mode+'-accepted')/'receipt.json',mode)
        if gate.check.sha(ADMISSION)!=pin:raise ValueError('admission changed during validation')
        if gate.check.sha(Path(__file__))!=collector_pin:raise ValueError('collector changed during validation')
        if CONFIGURATION_SOURCE and gate.check.sha(CONFIGURATION_SOURCE)!=configuration_pin:raise ValueError('configuration source changed during validation')
        receipt={'status':'pass','baseline':BASELINE,'coverage_input_sha256':gate.hashlib.sha256(raw).hexdigest(),'admission_sha256':pin,'admitted_receipts':pins,'collector_sha256':collector_pin,'configuration_sha256':configuration_pin,'outputs':{n:gate.check.sha(a.output/n) for n in ['census-updated.json','coverage-updated.json','delta.json']},'runtime_gate_pass':False}
        (a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(delta))
if __name__=='__main__':main()
