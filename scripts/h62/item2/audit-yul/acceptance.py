#!/usr/bin/env python3
"""Structural audit acceptance, not a proof or final runtime gate."""
import argparse, collections, hashlib, json, pathlib, re
ap=argparse.ArgumentParser();ap.add_argument('census',type=pathlib.Path);ap.add_argument('--output',type=pathlib.Path,required=True);args=ap.parse_args()
x=json.loads(args.census.read_text());rows=x['declarations'];ids=[r['id'] for r in rows]
assert len(ids)==len(set(ids))
assert x['frozen_blobs_verified'] and not x['unmatched_patterns']
assert len(x['files'])==1960 and x['parser_files']==1960
assert collections.Counter(r['kind'] for r in rows)=={'theorem':19230,'structure':268,'example':1887}
public=[r['source_name'] for r in rows if r['kind']=='theorem' and r['visibility']=='public'];assert len(public)==len(set(public))
assert sum(r['witness_status']=='joint_witness_proved' for r in rows)==3
assert sum(r['witness_status']=='joint_witness_impossible' for r in rows)==1
assert sum(r['witness_status']=='refutation_candidate_requires_check' for r in rows)==10
for r in rows:
 assert hashlib.sha256(r['signature'].encode()).hexdigest()==r['signature_sha256']
 if r['witness_status'] in ('joint_witness_proved','joint_witness_impossible'):
  assert r['signature_status']=='lean_parser_confirmed_source_span'
 if r['signature_status']=='lean_parser_confirmed_source_span':
  assert not re.search(r'\blet\s+\w+\s*$',r['signature'])
assert sum(r['signature_status']=='lexical_candidate_only' for r in rows)==302
args.output.mkdir(parents=True,exist_ok=True)
uncovered=[dict(id=r['id'],theorem=r['source_name'],owner=r['owner'],owner_basis=r['owner_basis'],status=r['witness_status']) for r in rows if r['kind']=='theorem' and r['witness_status']!='joint_witness_proved']
(args.output/'uncovered-statements.json').write_text(json.dumps(uncovered,indent=2,sort_keys=True)+'\n')
result=dict(structural_acceptance='pass',named_theorems=19230,joint_witnesses=3,uncovered_named_theorems=len(uncovered),impossible_proved=1,refutation_candidates=10,scope_decision='Q-REFUTATION-01 pending',final_gate='pending',runtime_gate_pass=False)
(args.output/'acceptance.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,sort_keys=True))
