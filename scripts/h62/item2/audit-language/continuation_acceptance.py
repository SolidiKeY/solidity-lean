#!/usr/bin/env python3
"""Regressions for strict partial-overlay receipts and narrow source refinements.
No original edits, patch application, Lean/server or inhabitance claims.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
from overlay_review import review,reconstruct,fidelity,TRUSTED,receipt_patch_path
from refine_remaining import replacement,lexical_namespaces,BASELINE_SHA256
from classify import declaration_index
from census import BASE,git

p=argparse.ArgumentParser(description=__doc__);p.add_argument("--registry",type=Path,required=True);p.add_argument("--baseline",type=Path,required=True);p.add_argument("--classification",type=Path,required=True);p.add_argument("--output",type=Path,required=True);args=p.parse_args()
if args.output.resolve().is_relative_to(Path(__file__).resolve().parents[4]):raise ValueError("bulk evidence must stay outside repository")
rows=json.loads(args.registry.read_text());reports=[review(r) for r in rows]
assert sum(r["theorem_headers"] for r in reports)==102
assert all(not r["patch_applied"] and r["ownership_agreement"]=="not-established-by-relay" and r["Lean_validation"].startswith("pending") for r in reports)
controls=[]
def reject(label,call):
 try:call()
 except ValueError as error:controls.append({"control":label,"status":"expected-rejection","reason":str(error)})
 else:raise AssertionError("negative control accepted: "+label)

first=rows[0];path=TRUSTED[first["label"]]["path"];original=git("show",f"{BASE}:{path}");patch=receipt_patch_path(first).read_bytes()
reject("wrong-original-blob",lambda:reconstruct(patch.replace(b"index b54c93a5b",b"index 000000000"),original,path))
reject("wrong-postimage-blob",lambda:reconstruct(patch.replace(b"..092971eda",b"..000000000"),original,path))
reject("context-drift-no-fuzz",lambda:reconstruct(patch.replace(b"   | cons a l ih =>",b"   | cons WRONG l ih =>",1),original,path))
reject("truncated-hunk",lambda:reconstruct(patch[:-80],original,path))
reject("extra-file",lambda:reconstruct(patch+b"diff --git a/extra b/extra\n",original,path))
reject("path-traversal",lambda:reconstruct(patch.replace(b"a/Solidity/Hash/CollisionBound.lean",b"a/../Solidity/Hash/CollisionBound.lean"),original,path))
changed=original.replace(b"(hb : b < N)",b"(hb : b <= N)",1)
assert changed!=original
reject("changed-frozen-premise",lambda:fidelity(path,original,changed))
reject("changed-proof-budget",lambda:fidelity(path,original,original+b"\nset_option maxHeartbeats 999999\n"))
forged=copy.deepcopy(first);forged["owner"]="invented-owner"
reject("forged-owner-metadata",lambda:review(forged))
fixed_receipt=next(r for r in rows if r['label']=='fixedpoint')
transcription=receipt_patch_path(fixed_receipt).with_name(TRUSTED['fixedpoint']['sha256']+'-fixedpoint-received.patch')
if transcription.exists():
 wrong=copy.deepcopy(fixed_receipt);wrong['path']=str(transcription)
 wrong['path_relative_to_evidence']=str(Path(fixed_receipt['path_relative_to_evidence']).with_name(transcription.name))
 reject("initial-local-transcription-not-authenticated",lambda:review(wrong))

fixture={"Solidity/AST.lean":"namespace Solidity\ninductive PrimTy where\n  | bool\n  | uint\n  | int\nend Solidity\n", "Solidity/Semantics.lean":"namespace Solidity\ndef PrimTy.Denote : PrimTy → Type\n  | .bool => Bool\n  | .uint => {n : Int // True}\n  | .int => {n : Int // True}\nend Solidity\n", "wrong.lean":"namespace Other\ninductive PrimTy where\n  | uint\nend Other\n"}
symbols,tails=declaration_index(fixture)
facts={key:{"label":key} for key in ['constructors','denote','address','world-word','semantics-word','fx']}
def binder(domain,role='source-sort-unresolved',refs=None):
 return {"domain":domain,"role":role,"definition_evidence":refs or []}
annotation=replacement(binder('PrimTy.uint.Denote'),{},'Solidity.Bridge.Arith',symbols,tails,facts)
assert annotation['role']=='refined-data-parameter' and annotation['constraint_source']=='PrimTy.uint.inRange n = true'
boolean=replacement(binder('PrimTy.bool.Denote'),{},'Solidity',symbols,tails,facts)
assert boolean['role']=='data-parameter' and boolean['carrier']=='Bool'
family_ref=next(k for k,r in symbols.items() if r['name']=='Solidity.PrimTy.Denote')
generic=replacement(binder('p.Denote','data-parameter',refs=[family_ref]),{'p':{'domain':'PrimTy'}},'Solidity',symbols,tails,facts)
assert generic['role']=='computed-data-parameter' and generic['branch_sensitive']
assert replacement(binder('p.Denote','data-parameter'),{'p':{'domain':'PrimTy'}},'Solidity',symbols,tails,facts) is None
assert replacement(binder('p.Denote','data-parameter',refs=[family_ref]),{'p':{'domain':'Bool'}},'Solidity',symbols,tails,facts) is None
assert replacement(binder('p.Denote','data-parameter',refs=[family_ref]),{},'Solidity',symbols,tails,facts) is None
for shadow in ('PrimTy','Solidity'):
 assert replacement(binder('p.Denote','data-parameter',refs=[family_ref]),{'p':{'domain':'PrimTy'},shadow:{'domain':'Type'}},'Solidity',symbols,tails,facts) is None
assert replacement(binder('PrimTy.uint.Denote'),{'PrimTy':{'domain':'Type'}},'Solidity',symbols,tails,facts) is None
assert replacement(binder('PrimTy.uint.Denote'),{},'Other',symbols,tails,facts) is None
contexts=lexical_namespaces('namespace N\ntheorem X.y : True := True.intro\nend N\nnamespace _root_.Q\ntheorem z : True := True.intro\nend Q\n')
assert contexts[2]=='N' and contexts[5] is None
address={'id':'address','name':'Solidity.ContractWorld.Address','path':'Solidity/Semantics/ContractWorld.lean'};symbols['address']=address
assert replacement(binder('Nat → Address',refs=['address']),{},'Solidity.ContractWorld',symbols,tails,facts) is None
assert replacement(binder('Address',refs=['address']),{},'Solidity.ContractWorld',symbols,tails,facts)['role']=='refined-data-parameter'
fx={'id':'fx','name':'Solidity.Language.FixedPoint.Fx','path':'Solidity/Language/FixedPoint.lean'};symbols['fx']=fx
assert replacement(binder('Fx t','data-parameter',refs=['fx']),{},'Solidity.Language.FixedPoint',symbols,tails,facts)['role']=='refined-data-parameter'
assert replacement(binder('Solidity.Language.FixedPoint.Fx t','data-parameter',refs=['fx']),{'Solidity':{'domain':'Type'}},'Solidity.Language.FixedPoint.Examples',symbols,tails,facts) is None
assert replacement(binder('Fx t','data-parameter',refs=['fx']),{},'Solidity.Language.FixedPointOther',symbols,tails,facts) is None

payload=args.baseline.read_bytes();assert hashlib.sha256(payload).hexdigest()==BASELINE_SHA256
before=json.loads(payload);after=json.loads(args.classification.read_text());assert not after['summary']['semantic_classification_complete'] and after['summary']['new_witness_claims']==0
assert after['remaining_pass']['generator_sha256']==hashlib.sha256(Path(__file__).with_name('refine_remaining.py').read_bytes()).hexdigest()
assert len(after['declarations'])==4146 and [r['source_id'] for r in before['declarations']]==[r['source_id'] for r in after['declarations']]
for old,new in zip(before['declarations'],after['declarations']):
 assert old['owner']==new['owner'] and old['signature_sha256']==new['signature_sha256']
 assert new['in_scope'] and new['exclusion'] is None and old['conclusion_source']==new['conclusion_source']
 for group in ['section_context','explicit_and_leading_binders']:
  assert len(old[group])==len(new[group])
  for a,b in zip(old[group],new[group]):
   for key in a:
    if key not in ('sort','role','inhabitance'):assert a[key]==b[key],(new['source_id'],key)
changes=after['remaining_pass']['changes'];keys=[(c['source_id'],c['group'],c['ordinal']) for c in changes];assert len(keys)==len(set(keys))
fact_labels={f['label'] for f in after['remaining_pass']['facts'].values()}
for c in changes:assert set(c['evidence']['fact_labels'])<=fact_labels
for f in after['remaining_pass']['facts'].values():
 source=git('show',f"{BASE}:{f['path']}")
 assert hashlib.sha256(source).hexdigest()==f['file_sha256']
 assert source.decode().count(f['excerpt'])==1
 assert hashlib.sha256(f['excerpt'].encode()).hexdigest()==f['excerpt_sha256']
args.output.mkdir(parents=True,exist_ok=True)
(args.output/'negative-controls.json').write_text(json.dumps(controls,indent=2)+'\n')
print(json.dumps({'status':'PASS-source-receipts-and-refinements-only','negative_controls':len(controls),'source_rows':4146,'binder_refinements':len(changes),'overlays_applied':False,'new_witnesses':0}))
