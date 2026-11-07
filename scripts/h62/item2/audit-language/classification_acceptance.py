#!/usr/bin/env python3
"""Source-classifier acceptance, including the actual review attacks.
No Lean/server calls. Positive source roles do not certify feasibility.
"""
import argparse
import collections
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
from classify import (signature_parts,result_spine,declaration_index,source_sort,
                      owner_roles,generate)

p=argparse.ArgumentParser(description=__doc__)
p.add_argument("--classification",type=Path,required=True)
p.add_argument("--census",type=Path,required=True)
p.add_argument("--output",type=Path,required=True)
args=p.parse_args()
if args.output.resolve().is_relative_to(Path(__file__).resolve().parents[4]):
 raise ValueError("bulk acceptance output must be outside the repository")
args.output.mkdir(parents=True,exist_ok=True)

# Independent literal fixtures reproduce concrete review findings.
header,result=signature_parts("theorem example {M a : Int} (h : 0 ≤ a) : a < M → a = a")
leading,conclusion=result_spine(result)
assert [b["name"] for b in header]==["M","a","h"]
assert [b["domain"] for b in leading]==["a < M"] and conclusion=="a = a"
for text in ["A ↔ B → C","A -> B <-> C","∃ n, ∀ fuel, P n fuel → Q n fuel"]:
 assert result_spine(text)[0]==[],text
assert len(result_spine("∀ (n : Nat), P n → Q n")[0])==2

fixture="""namespace N
structure Plain where
  value : Nat := 0
  enabled : Bool := true
structure Certified where
  value : Nat
  bound : value < 4
  all : ∀ n : Nat,
    n = n
structure Law : Prop where
  valid : True
structure Spec where
  Input : Type
  WellFormed : Input → Prop
structure Validator (S : Spec) where
  validate : S.Input → Bool
  sound : ∀ i,
    validate i = true → S.WellFormed i
end N
namespace Other
structure Plain where
  valid : True
end Other
"""
symbols,tails=declaration_index({"fixture.lean":fixture})
used={}
def sort(domain,namespace="N",local=None):
 return source_sort(domain,namespace,local or {},symbols,tails,used)
assert sort("Nat → Nat")[0]=="function-parameter"
assert sort("Nat → Prop")[0]=="predicate-parameter"
assert sort("∀ x y, x = y")[0]=="proof-premise"
assert sort("Plain")[0]=="structure-parameter",sort("Plain")
assert sort("Certified")[0]=="certificate-carrying-data",sort("Certified")
assert sort("Validator")[0]=="certificate-carrying-data",sort("Validator")
assert sort("Plain","Unrelated")[0]=="ambiguous-source-symbol-unresolved"
assert sort("Law")[0]=="proof-premise"
plain=next(r for r in symbols.values() if r["name"]=="N.Plain")
assert all(":=" not in f["domain"] for f in plain["fields"])
assert any(f["default_source"]=="true" for f in plain["fields"])
cert=next(r for r in symbols.values() if r["name"]=="N.Certified")
assert "n = n" in next(f["domain"] for f in cert["fields"] if f["name"]=="all")

claims=[{"id":"A","owner":"same-owner","mode":"live-reservation"},
        {"id":"B","owner":"same-owner","mode":"live-reservation"},
        {"id":"H62-6-MIGRATE-X","owner":"migration","mode":"isolated-migration-overlay"}]
assert owner_roles(claims)["classification"]=="documented-live-owner"
assert owner_roles(claims)["live_producer_owners"]==["same-owner"]
assert owner_roles([{"id":"H62-1-FIXTURE","owner":"cleanup","mode":"exclusive-additive"}])["classification"]=="cleanup-writer-only-producer-unresolved"
assert owner_roles([])["classification"]=="no-documented-live-producer"

census=json.loads(args.census.read_text())
assert census==generate(),"acceptance input must be the frozen census"
report=json.loads(args.classification.read_text())
assert report["generator_sha256"]==hashlib.sha256(Path(__file__).with_name("classify.py").read_bytes()).hexdigest()
assert report["census_generator_sha256"]==hashlib.sha256(Path(__file__).with_name("census.py").read_bytes()).hexdigest()
expected={r["id"] for r in census["declarations"]}
actual=[r["source_id"] for r in report["declarations"]]
assert len(actual)==len(set(actual)) and set(actual)==expected
assert all(r["in_scope"] and r["exclusion"] is None for r in report["declarations"])
assert not report["parse_errors"] and not report["summary"]["semantic_classification_complete"]
assert report["summary"]["new_witness_claims"]==0
assert report["summary"]["owner_files"]=={"documented-live-owner":127,"cleanup-writer-only-producer-unresolved":18,"no-documented-live-producer":244}
assert report["summary"]["owner_declarations"]=={"documented-live-owner":1270,"cleanup-writer-only-producer-unresolved":105,"no-documented-live-producer":2771}
by_name={r["target_name_candidate"]:r for r in report["declarations"]}
def row_ending(suffix):
 hits=[r for name,r in by_name.items() if name.endswith(suffix)]
 assert len(hits)==1,suffix
 return hits[0]
validator=row_ending("Validator.ctxRefines_back")
T=next(b for b in validator["explicit_and_leading_binders"] if b["name"]=="T")
hv=next(b for b in validator["explicit_and_leading_binders"] if b["name"]=="hv")
assert T["role"]=="certificate-carrying-data"
assert "global-conditional-validator-contract" in T["reviewed_premise_scopes"]
assert hv["role"]=="proof-premise" and hv["domain"]=="T.validate i art = true"
store=row_ending("Memory.store_refines")
hp=next(b for b in store["explicit_and_leading_binders"] if b["name"]=="hp")
assert hp["reviewed_premise_scopes"]==["global-bounded-allocator-law"]
assert any(b["name"]=="hb" and b["role"]=="proof-premise" for b in store["explicit_and_leading_binders"])
assert any(d["kind"]=="omit" for r in report["declarations"] if r["path"]=="Solidity/Hash/Adaptive.lean" for d in r["source_directive_history"])

# Modified bulk JSON must be rejected before symbol indexing/output writes.
attacks=[]
for kind in ("owner","signature","omitted-candidate"):
 corrupted=copy.deepcopy(census)
 if kind=="owner":
  path=next(path for path,meta in corrupted["sources"].items() if meta["ownership_claims"])
  corrupted["sources"][path]["ownership_claims"][0]["owner"]="invented-owner"
 elif kind=="signature": corrupted["declarations"][0]["source_signature"]="theorem invented : True"
 else: corrupted["declarations"].pop()
 bad=args.output/(kind+"-census.json")
 bad.write_text(json.dumps(corrupted))
 command=["python3",str(Path(__file__).with_name("classify.py")),"--census",str(bad),"--output",str(args.output/(kind+"-unexpected"))]
 result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1"))
 assert result.returncode!=0 and "census differs from frozen source or pinned ownership snapshot" in result.stdout,(kind,result.stdout)
 assert not (args.output/(kind+"-unexpected")).exists()
 (args.output/(kind+"-rejection.log")).write_text(result.stdout)
 bad.unlink()
 attacks.append({"attack":kind,"command":command,"exit":result.returncode,"expected_rejection":True})
(args.output/"negative-controls.json").write_text(json.dumps(attacks,indent=2)+"\n")
print(json.dumps({"status":"PASS-source-classification-only","declarations":len(actual),"excluded":0,
                  "negative_controls":len(attacks),"semantic_certification":False},sort_keys=True))
