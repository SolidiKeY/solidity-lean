#!/usr/bin/env python3
"""Guard defaulted Source RuntimePlan type drift being hidden by unchanged headers.

Reparse only the exact executed failed-gate probe below; success here is an
observation, never proof acceptance. Keep original Source identities pending.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
PROBE_SHA='164ad815748f277e78d3b16451fe1df43bf8159fd9a4e233753469335463e469'
CANONICAL='532234a73caefaadee0ef39a75108d9392b6de99e05fcbd763ce9634642c9077'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def private_output(path):
    output=path.resolve()
    if output.is_relative_to(ROOT):
        raise ValueError('evidence output must remain outside public checkout')
    return output

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--proof-root',type=Path,required=True);p.add_argument('--ledger',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    a.output=private_output(a.output)
    ledger=a.ledger.read_bytes();raw=(a.proof_root/'probe.log').read_bytes()
    if sha(ledger)!=CANONICAL or sha(raw)!=PROBE_SHA:raise ValueError('unadmitted census/probe')
    spec=importlib.util.spec_from_file_location('statement_drift_gate',Path(__file__).with_name('check_read_statements.py'))
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);g=m.gate
    frozen=json.loads(ledger);by={r['source_name']:r for r in frozen['declarations']}
    names=m.ALL_INTERFACES
    if len(by)!=792 or len(names)!=6:raise ValueError('original/selection membership drift')
    selected={'base':g.original.BASE,'modules':[{'file':f} for f in sorted({by[n]['file'] for n in names})],'declarations':[by[n] for n in names]}
    observed=g.original.export.collect(raw.decode(),selected)
    source=a.proof_root/'staged/PrimitiveTransportWitnesses.lean'
    if source.read_bytes()!=(ROOT/g.SOURCE).read_bytes():raise ValueError('executed witness source differs')
    captures={}
    for file in (a.proof_root/'captured').rglob('*.lean'):
        relative=str(file.relative_to(a.proof_root/'captured'));buf=file.read_bytes()
        if buf!=(ROOT/relative).read_bytes():raise ValueError('executed dependency source drift')
        captures[relative]=sha(buf)
    axioms=g.joint.parse_axioms(raw.decode(),g.PREFIX,g.NAMES)
    rows=[]
    for r in observed['declarations']:
        old=by[r['source_name']];equal=r['raw_type_sha256']==old['elaborated']['raw_type_sha256']
        rows.append({'source_name':r['source_name'],'owner':old['owner'],'file':old['file'],'original_raw_type_sha256':old['elaborated']['raw_type_sha256'],'current_raw_type_sha256':r['raw_type_sha256'],'types_equal':equal,'original_signature_sha256':old['signature_sha256'],'original_credit_added':False})
    if sum(not r['types_equal'] for r in rows)!=4:raise ValueError('review exact drift set')
    a.output.mkdir(parents=True,exist_ok=False)
    (a.output/'types.json').write_text(json.dumps(observed,indent=2)+'\n')
    result={'status':'observed-type-drift','originals':792,'cases':rows,'source_sha256':sha(source.read_bytes()),'probe_sha256':sha(raw),'dependency_sources':captures,'audit_axioms':axioms,'source_compile_stage':'completed before strict collector refused type drift; whole original gate failed','witness_theorems':19,'current_kernel_type_matches':2,'current_kernel_type_drifts':4,'statement_or_definition_edits':0,'original_credit_added':0,'semantic_equivalence_proved':False,'runtime_gate_pass':False}
    (a.output/'drift.json').write_text(json.dumps(result,indent=2)+'\n')
    options='options: owner publishes H57 legacy/planned versioned pairs with consumer transports; owner supplies exact semantic bridge and retains original pending identities until checked'
    (a.output/'ESCALATIONS.txt').write_text(''.join('ESCALATE: '+r['source_name']+' frozen/current raw kernel type differs; evidence '+str(a.output/'drift.json')+'; '+options+'\n' for r in rows if not r['types_equal']))
    print(json.dumps({'types_equal':2,'types_drifted':4,'credit':0,'output':str(a.output)}))
if __name__=='__main__':main()
