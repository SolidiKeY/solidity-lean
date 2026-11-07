#!/usr/bin/env python3
"""Acceptance for source parser spans, proof separators and failure status.

The sole Lean subprocess is a negative parser-input test. No frozen source is
elaborated; these are external tooling checks, not feasibility proofs.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
import os
import pathlib
import subprocess

p=argparse.ArgumentParser(description=__doc__)
p.add_argument("--evidence",type=pathlib.Path,required=True)
p.add_argument("--lean",type=pathlib.Path,required=True)
a=p.parse_args()
root=pathlib.Path(__file__).resolve().parents[4]
evidence=a.evidence.resolve()
spec=importlib.util.spec_from_file_location("reconcile",root/"scripts/h62/item2/audit-memory-operations/reconcile.py")
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
source=json.loads(pathlib.Path('/workspace/h62-audit-memory-evidence/census.json').read_text())
prior=json.loads(pathlib.Path('/workspace/h62-audit-memory-h70-evidence/reconciled-census.json').read_text())
headers=json.loads((evidence/'all-theorems-final/headers.json').read_text())
subset=json.loads((evidence/'compiler23/headers.json').read_text())
parsed=r.validate_parsed_headers(source,headers)
expected={i for i,row in enumerate(source['declarations']) if row['kind'] in ('theorem','lemma')}
assert set(parsed)==expected and len(parsed)==3932
unresolved={i for i,row in enumerate(prior['declarations']) if not row['premise_bundle']['header_source']}
assert unresolved==set(r.validate_parsed_headers(source,subset)) and len(unresolved)==23
for item in subset['results']:
    full=parsed[item['source_id']]
    for key in ('header_source','header_end','header_end_utf8','source_region_sha256','header_sha256'):
        assert item[key]==full[key]
assert sum(h['header_end_utf8']!=h['header_end'] for h in parsed.values())==2647
for index in (24,2204,4123):
    assert parsed[index]['proof_separator']=='where'
    assert len(parsed[index]['header_source'])<len(prior['declarations'][index]['premise_bundle']['header_source'])
for problem in ('duplicate','identity','source-hash','header-text','utf8','syntax-kind','count','credit'):
    bad=copy.deepcopy(headers)
    if problem=='duplicate':bad['results'].append(copy.deepcopy(bad['results'][0]))
    if problem=='identity':bad['identities'][0]['source_name']='wrong'
    if problem=='source-hash':bad['results'][0]['source_region_sha256']='0'*64
    if problem=='header-text':bad['results'][0]['header_source']+='altered'
    if problem=='utf8':bad['results'][0]['header_end_utf8']+=1
    if problem=='syntax-kind':bad['results'][0]['syntax_kind']='term'
    if problem=='count':bad['counts']['requested']-=1
    if problem=='credit':bad['counts']['kernel_signatures']=1
    try:r.validate_parsed_headers(source,bad)
    except ValueError:pass
    else:raise AssertionError('failed open: '+problem)

# A malformed source signature must save its parse error and return nonzero.
fixture=evidence/'malformed-source.txt'
text='theorem malformed (x : Nat) :\n  (\n'
fixture.write_text(text)
request=dict(declarations=[dict(kind='theorem',path=str(fixture),line=1,name='malformed',
    source_start=0,source_end=len(text),source_command_region=text,premise_bundle=dict(header_source=''))])
negative=evidence/'negative-census.json';negative.write_text(json.dumps(request)+'\n')
cmd=['python3','scripts/h62/item2/audit-memory-operations/parse-headers.py','--lean',str(a.lean),
    '--census',str(negative),'--evidence',str(evidence/'negative-parser')]
proc=subprocess.run(cmd,cwd=root,capture_output=True,text=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
(evidence/'negative-cli.log').write_text(proc.stdout+proc.stderr)
assert proc.returncode==1
negative_result=json.loads((evidence/'negative-parser/headers.json').read_text())
assert negative_result['counts']['requested']==1 and negative_result['counts']['parse_errors']==1
assert negative_result['results'][0]['status']=='parse-error'
negative_command=json.loads((evidence/'negative-parser/command.json').read_text())
assert negative_command['exit']==0 and negative_command['result_exit']==1

ownerpath=pathlib.Path('/workspace/h62-coordinator-inputs/ownership.json')
owners=json.loads(ownerpath.read_text())
routes=json.loads((root/'tests/h62/item2/audit-memory-operations/owner-routes.json').read_text())
result=r.reconcile(root,source,routes,owners,ownerpath,headers)
assert result['counts']['parser_source_signatures']==3932
assert result['counts']['unresolved_source_headers']==0
assert result['counts']['kernel_verified_signatures']==0
assert result['counts']['verified_witnesses']==0
assert result['counts']['public_compiler_contract_credits']==0
assert [(d['path'],d['line'],d['name']) for d in result['declarations']]==[(d['path'],d['line'],d['name']) for d in source['declarations']]
paths=['Solidity/Backend/MemoryCopies/CopyPathInterface.lean','Solidity/Backend/MemoryCopies/CopyPaths.lean']
copyrows=[dict(source_id=i,**row) for i,row in enumerate(result['declarations']) if row['path'] in paths]
assert {row['path'] for row in copyrows}==set(paths)
inventory=dict(boundary='Frozen source inventory only; exact kernel signatures and owner agreement pending',
    modules=[m for m in result['modules'] if m['path'] in paths],declarations=copyrows,
    ticket_destinations=['solidity-copy-recovery-20261030/memory-storage-copy','solidity-v07-v11-20261030/v11-memory-operations'],
    delivery_status='coordinator reports delivery pending none; not owner agreement',
    exact_file_owner=None,ownership_agreement='pending V11/CR reply; no original-file permission',
    kernel_feasibility='pending compatible migration overlays')
(evidence/'copypaths-inventory.json').write_text(json.dumps(inventory,indent=2,ensure_ascii=False)+'\n')
(evidence/'negative-test-command.json').write_text(json.dumps(dict(command=cmd,exit=proc.returncode,expected_exit=1),indent=2)+'\n')
print('PASS: 3932 exact source prefixes, all23 resolved,2647 UTF8-sensitive spans,3 where-proof boundaries, preserved4141 identities, malformed input exits1, forged metadata rejected, zero kernel/proof credits; CopyPaths inventory retains pending ownership')
