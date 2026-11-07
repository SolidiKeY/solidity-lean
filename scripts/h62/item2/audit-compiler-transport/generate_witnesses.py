#!/usr/bin/env python3
"""Deterministic per-declaration audit drivers; generated bulk stays off Git.

Empty, deliberate negative, and constructive-search cases have distinct proof
paths. Neither a negative conclusion nor search failure justifies an exemption.
"""
import argparse
import hashlib
import json
from pathlib import Path
from census import generate

ap=argparse.ArgumentParser()
ap.add_argument('--root',type=Path,default=Path.cwd())
ap.add_argument('--reflected',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
ap.add_argument('--classification',type=Path,default=Path('tests/h62/item2/audit-compiler-transport/h69-classification.json'))
a=ap.parse_args()
source=generate(a.root.resolve())
modules=[r['module'][:-5].replace('/','.') for r in source['modules']]
rows=[]
for p in sorted(a.reflected.glob('*.json')):rows.extend(json.loads(p.read_text()))
rows.sort(key=lambda r:(r['module'],r['kernel_name']))
assert len({r['kernel_name'] for r in rows})==len(rows)
classification=json.loads(a.classification.read_text())
negative={r['source_name'] for r in classification['negative_controls']}
known={'Solidity.Backend.Passes.'+n for n in ['compilation_exact','compilation_success','compilation_reflect_success','compilation_revert_iff','compilation_input_stack']}
a.output.mkdir(parents=True,exist_ok=True)
results=a.output/'results';results.mkdir(exist_ok=True)
imports='\n'.join('import '+m for m in modules)
imports+='\nimport tests.h62.item2.«audit-compiler-transport».H69\n'
imports+='import tests.h62.item2.«audit-compiler-transport».AutoWitness\n'
empty=[];search=[];impossible=[];inventory=[]
for i,row in enumerate(rows):
    name=row['kernel_name'];qid=json.dumps(name)
    item={'kernel_name':name,'source_name':row['source_name'],'source_type_sha256':hashlib.sha256(row['raw_type'].encode()).hexdigest(),'declaration_kind':row['declaration_kind']}
    if row['source_name'] in negative:
        item['mode']='classified-h69-impossibility'
        classification_row=next(c for c in classification['negative_controls'] if c['source_name']==row['source_name'])
        if classification_row.get('declaration_role')=='generated-infeasible-branch-helper':
            proof=classification_row['proof']
            impossible.append('theorem '+proof+' : ¬ jointHypothesesStr% '+qid+' := jointImpossibleStr% '+qid+'\n#print axioms '+proof)
    elif row['source_name'] in known:
        item['mode']='existing-correlated-boundary-witness'
    elif not row['binders']:
        assert row['telescope_result']!='False','closed False declaration requires immediate investigation'
        item['mode']='empty-external-telescope'
        item['proof']='H62.CompilerTransport.Generated.Empty'+str(i)
        empty.append('theorem '+item['proof']+' : jointHypothesesStr% '+qid+' := emptyJoint% '+qid+'\n#print axioms '+item['proof'])
    elif row['telescope_result']=='False':
        item['mode']='unreviewed-generated-negative'
    else:
        item['mode']='bounded-constructive-search'
        item['proof']='H62.CompilerTransport.Generated.W'+str(i)
        item['result_file']=str((results/(str(i)+'.json')).resolve())
        search.append('#audit_joint '+qid+' as '+item['proof']+' into '+json.dumps(item['result_file']))
    inventory.append(item)
(a.output/'EmptyWitnesses.lean').write_text(imports+'\n'+'\n'.join(empty)+'\n')
(a.output/'NegativeWitnesses.lean').write_text(imports+'\n'+'\n'.join(impossible)+'\n')
chunks=[]
for i in range(0,len(search),32):
    p=a.output/('WitnessBatch'+str(i//32)+'.lean')
    p.write_text(imports+'\n'+'\n'.join(search[i:i+32])+'\n')
    chunks.append(str(p.resolve()))
(a.output/'inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
(a.output/'batches.json').write_text(json.dumps(chunks,indent=2)+'\n')
print(json.dumps({'records':len(rows),'empty_checks':len(empty),'negative_checks':len(impossible),'search_cases':len(search),'batches':len(chunks)},sort_keys=True))
