#!/usr/bin/env python3
"""Source/typed census acceptance; never claims the full runtime gate."""
import argparse,collections,hashlib,json,pathlib,re
ap=argparse.ArgumentParser();ap.add_argument('census',type=pathlib.Path);ap.add_argument('--output',type=pathlib.Path,required=True);args=ap.parse_args()
x=json.loads(args.census.read_text());rows=x['declarations'];ids=[r['id'] for r in rows]
assert len(ids)==len(set(ids))
assert x['frozen_blobs_verified'] and not x['unmatched_patterns']
assert len(x['files'])==1960 and x['parser_files']==1960
assert collections.Counter(r['kind'] for r in rows)=={'theorem':19230,'structure':268,'example':1887}
public=[r['source_name'] for r in rows if r['kind']=='theorem' and r['visibility']=='public'];assert len(public)==len(set(public))
assert sum(r['witness_status']=='joint_witness_proved' for r in rows)==5
assert sum(r['witness_status']=='intentional_refutation_proved' for r in rows)==11
assert not any(r['witness_status'] in ('joint_witness_impossible','refutation_candidate_requires_check') for r in rows)
allowed={'propext','Classical.choice','Quot.sound'}
def file_sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
for r in rows:
 assert hashlib.sha256(r['signature'].encode()).hexdigest()==r['signature_sha256']
 status=r['witness_status']
 if status in ('joint_witness_proved','intentional_refutation_proved'):
  assert r['signature_status']=='lean_parser_confirmed_source_span'
  e=r['audit_evidence'];assert file_sha(e['proof_module'])==e['proof_source_sha256']
  attempts=[json.loads(l) for l in pathlib.Path(e['proof_gate']).read_text().splitlines()]
  matching=[g for g in attempts if g['command'][-1]==e['proof_module']]
  assert matching and matching[-1]['exit']==0 and matching[-1]['source_sha256']==e['proof_source_sha256']
  if status=='intentional_refutation_proved':assert e['audit_criterion']=='H69' and e['intentional_reason'] and e['proof']
  else:assert e['audit_criterion']=='joint_satisfiability'
  if e.get('control_snapshot'):
   assert file_sha(e['control_snapshot'])==e['control_snapshot_sha256']
   snapshot=json.load(open(e['control_snapshot']));assert snapshot['gate']['exit']==0
   assert snapshot['source']==e['proof_module'] and snapshot['source_sha256']==e['proof_source_sha256']
   assert snapshot['gate']==matching[-1]
   assert file_sha(snapshot['proof_tool'])==snapshot['proof_tool_sha256']==e['proof_tool_sha256']
   tools=[g for g in attempts if g['command'][-1]==snapshot['proof_tool']]
   assert tools and tools[-1]['exit']==0 and tools[-1]['source_sha256']==snapshot['proof_tool_sha256']
   assert snapshot['proof_tool_gate']==tools[-1]
   source_calls=re.findall(r'^audit_joint_defaults "([^"]+)"',pathlib.Path(snapshot['source']).read_text(),re.M)
   assert [c['theorem'] for c in snapshot['records']]==source_calls
   assert len(snapshot['records'])==6
   record=next(c for c in snapshot['records'] if c['theorem']==r['source_name'])
   assert record['proof']==e['proof'] and record['status']=='joint_witness_proved'
   assert hashlib.sha256(record['frozen_type_repr'].encode()).hexdigest()==e['frozen_type_sha256']
   assert r['kernel']['type_sha256']==e['frozen_type_sha256']
   assert len(record['values_repr'])==len(r['kernel']['binders'])
   assert record['level_parameters']==r['kernel']['level_parameters']
   assert set(record['axioms'])<=allowed
 if status=='closed_statement_verified':assert r['kind']=='theorem' and not r['kernel']['binders'] and set(r['kernel']['axioms'])<=allowed
 if r['signature_status']=='lean_parser_confirmed_source_span':assert not re.search(r'\blet\s+\w+\s*$',r['signature'])
assert sum(r['signature_status']=='lexical_candidate_only' for r in rows)==302
assert x['kernel_errors']==0 and file_sha(x['kernel_metadata_file'])==x['kernel_metadata_sha256']
accepted={'joint_witness_proved','intentional_refutation_proved','closed_statement_verified'}
args.output.mkdir(parents=True,exist_ok=True)
uncovered=[dict(id=r['id'],theorem=r['source_name'],owner=r['owner'],owner_basis=r['owner_basis'],status=r['witness_status'],kernel_status=r.get('kernel_status')) for r in rows if r['kind']=='theorem' and r['witness_status'] not in accepted]
(args.output/'uncovered-statements.json').write_text(json.dumps(uncovered,indent=2,sort_keys=True)+'\n')
negative=[dict(id=r['id'],theorem=r['source_name'],file=r['file'],line=r['line'],owner=r['owner'],signature=r['signature'],kernel_type=r['kernel']['pretty_type']) for r in rows if r['kind']=='theorem' and r.get('kernel',{}).get('result_is_false') and r['witness_status'] not in accepted]
(args.output/'pending-negative-classification.json').write_text(json.dumps(negative,indent=2,sort_keys=True)+'\n')
result=dict(structural_acceptance='pass',named_theorems=19230,joint_witnesses=5,intentional_refutations=11,closed_theorems=sum(r['kind']=='theorem' and r['witness_status']=='closed_statement_verified' for r in rows),uncovered_named_theorems=len(uncovered),pending_negative_classifications=len(negative),typed_source_declarations=sum(r.get('kernel_status')=='matched' for r in rows),typed_source_structures=sum(r['kind']=='structure' and r.get('kernel_status')=='matched' for r in rows),scope_decision='Q-REFUTATION-01 resolved by H69',synthetic_controls_counted=0,final_gate='pending',runtime_gate_pass=False)
(args.output/'acceptance.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,sort_keys=True))
