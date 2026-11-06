#!/usr/bin/env python3
"""Consolidate existing exports only. Does not run Lean or assert visibility.

No generated family or private-looking name is excluded. Kernel expression text
preserves universe/binder representation; H78 visibility and new signatures
remain explicitly unverified until authoritative exports become available.
"""
import argparse
import hashlib
import json
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--raw',type=Path,required=True)
p.add_argument('--normalized',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
p.add_argument('--source-base',required=True)
p.add_argument('--capture-report',type=Path,required=True)
a=p.parse_args()
if a.out.exists(): raise SystemExit('Refusing reused export')
capture=json.loads(a.capture_report.read_text())
if capture.get('complete') is not True or capture['settings']['mode']!='interface-fixture':
    raise SystemExit('Capture report is not a successful interface fixture')
reference=json.loads(a.normalized.read_text())['declarations']
with a.raw.open() as f:
    entries=json.loads(next(line for line in f if line.startswith('[')))
if len(entries)!=len(reference) or {e['name'] for e in entries}!=set(reference) or len({e['name'] for e in entries})!=len(entries):
    raise SystemExit('Declaration coverage/uniqueness mismatch')
families=['noConfusion','recOn','casesOn','match_','toCtorIdx','_proof_']
counts={name:0 for name in families}
records=[]
for e in sorted(entries,key=lambda e:e['name']):
    digest=hashlib.sha256(json.dumps([e['levelParams'],e['typeExpr']],sort_keys=True,separators=(',',':')).encode()).hexdigest()
    if digest!=reference[e['name']]['type_sha256']:
        raise SystemExit('Signature mismatch: '+e['name'])
    if e['kind']!=reference[e['name']]['kind'] or e['module']!=reference[e['name']]['module']:
        raise SystemExit('Kind/module mismatch: '+e['name'])
    candidates=[family for family in families if any(part.startswith(family) for part in e['name'].split('.'))]
    for family in candidates: counts[family]+=1
    records.append({'name':e['name'],'module':e['module'],'old_signature':{'universe_parameters':e['levelParams'],'kind':e['kind'],'kernel_type_expression':e['typeExpr'],'type_sha256':digest},'visibility':{'status':'not_recorded','reason':'Existing capture did not export visibility metadata; no visibility inference from naming.'},'generated_family_name_candidates':candidates,'new_signature':None,'shim_signature':None})
h=hashlib.sha256()
with a.raw.open('rb') as f:
    for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
data={'schema_version':1,'source_base_claim':a.source_base,'source_capture_report':str(a.capture_report.resolve()),'source_versions':capture['versions'],'provenance_boundary':'Base is the caller-supplied authenticated-capture label, not inferred from expression text.','source_raw':str(a.raw.resolve()),'source_raw_sha256':h.hexdigest(),'total_records':len(records),'excluded_records':0,'generated_family_name_candidate_counts':counts,'public_inventory_complete':False,'new_exports_available':False,'implemented_shims':[],'acceptance':'PENDING_H78_VISIBILITY_AND_NEW_EXPORTS; not compatibility evidence','records':records}
with a.out.open('x') as f: json.dump(data,f,sort_keys=True); f.write('\n')
print(json.dumps({k:v for k,v in data.items() if k!='records'},indent=2))
