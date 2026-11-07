#!/usr/bin/env python3
"""Eight Pure premise-role records plus a checked44-record cumulative union.
All26 original Pure declarations remain accounted; this inventories only eight
selected interfaces, adds no witnesses and dispositions no generated candidate.
"""
import argparse,json,os,subprocess,sys
from collections import Counter
from pathlib import Path
from census import ROOT,BASE,scan
from input_roles import annotate,digest
from assignable_input_roles import SPECS as ASSIGNABLE
from mutability_input_roles import SPECS as CLOSER_PAYABLE
from input_roles import SPECS as BRIDGE_OUTCOME
import verify_census as v
SPECS={}
def add(name,binders,config,premises,notes):
    SPECS["Solidity.Theory.Mutability."+name]={"binders":binders.split(),"configuration":config.split(),"premises":premises,"notes":notes}
for name,binders in[("withOutside_outside","C Γ σ"),("outside_withOutside","C Γ σ w"),("withOutside_withOutside","C Γ σ w w'")]:
    add(name,binders,"C Γ",{},"No logical premise. State and outside structures are correlated data, not global feasibility or pure-program admission laws. Concrete populated storage and an observable outside replacement supply real inputs; no program/compiler totality follows from these record laws.")
add("TRes.map_map","α β γ f g x","α β γ",{},"Function and result inputs are data, not universally successful-computation premises. The packet uses Nat types, nonconstant functions and an actual .ok value, rather than only mapping an error or an empty type.")
for name,binders in[("TLoop.step_map","α β f body c body' c' hb hc a"),("TLoop.iterN_map","α β f body c body' c' hb hc n a"),("TLoop.run_map","α β f body c body' c' hb hc a")]:
    add(name,binders,"α β",{"hb":"global-all-input-body-commutation-for-fixed-functions","hc":"global-all-input-condition-commutation-for-fixed-functions"},"hb and hc quantify EVERY alpha input for the SAME selected f/body/c/body'/c', not just selected a, and not all possible function choices. They must coexist with actual a and any late iteration n. Nat successor map is nonidentity; both loops make a real step and terminate. The iterN budget is semantic iteration data, not a physical EVM gas bound; original run_map does not itself assert termination.")
ANON="a._@._internal._hyg.0"
add("Simple.evalT_withOutside",f"C Γ σ w p s {ANON}","C Γ",{ANON:"per-selected-value-no-state-read-check"},"The anonymous inherited premise is still present: this selected simple value reads no state. It is not a forall-expression purity law. The SAME populated state and changed outside coexist with the bool literal; this does not discharge later pure-program/call/callback contracts.")
FILE="Solidity/Theory/Mutability/Pure.lean"
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for n in("out","proof-evidence","historical-evidence"):ap.add_argument("--"+n,type=Path,required=True)
    a=ap.parse_args();out=a.out.resolve();proof=a.proof_evidence.resolve();old=a.historical_evidence.resolve()
    if any(p.is_relative_to(ROOT)for p in(out,proof,old)):raise SystemExit("Use off-Git evidence")
    out.mkdir(parents=True,exist_ok=True)
    cmd=[sys.executable,str(Path(__file__).resolve().with_name("assignable_input_roles.py")),"--out",str(out),"--proof-evidence",str(proof),"--historical-evidence",str(old)]
    x=subprocess.run(cmd,cwd=ROOT,env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1"),capture_output=True,text=True);assert x.returncode==0,(x.stdout,x.stderr)
    source=old/"verified-census.json";manifest=dict((line.split("  ",1)[1],line.split("  ",1)[0])for line in(old/"SHA256SUMS").read_text().splitlines());assert digest(source)==manifest[source.name]
    historical=json.loads(source.read_text());assert historical["base"]==BASE
    originals={r["source_name"]:r for r in historical["declarations"]}
    frozen=subprocess.check_output(["git","show",BASE+":"+FILE],cwd=ROOT);assert(ROOT/FILE).read_bytes()==frozen
    selected={r["source_name"]:r for r in scan(frozen.decode(),FILE)};assert len(selected)==26 and set(SPECS)<=set(selected)and len(SPECS)==8
    assert{name for name in selected if name in v.WITNESSES}==set(SPECS)
    v.VERSION=json.loads((proof/"serial/baseline-results.json").read_text())["version"];v.FINGERPRINTS.clear();v.checked_module(proof/"serial",FILE)
    records=[];dispositions=[]
    for name in selected:
        orig=originals[name];assert orig["source_header"]==selected[name]["source_header"]
        row={k:orig[k]for k in("source_name","file","line","source_header","elaborated_type_sha256","documented_producing_lane","proving_owner")}
        if name in SPECS:
            cert=v.certificate(proof/"serial",*v.WITNESSES[name]);row.update(status="joint-witness-checked",current_joint_certificate=cert)
            report=annotate(orig,SPECS[name]);report.update(status="joint-witness-checked",current_joint_certificate=cert);records.append(report)
        elif orig["status"]=="no-inputs":row["status"]="historical-empty-input-telescope"
        else:row["status"]="original-input-witness-pending"
        dispositions.append(row)
    counts=dict(Counter(r["status"]for r in dispositions));assert counts=={"joint-witness-checked":8,"historical-empty-input-telescope":1,"original-input-witness-pending":17}
    companion=out/"all-reviewed-input-roles.json";previous=json.loads(companion.read_text())
    assert previous["frozen_assignment_base"]==BASE and previous["historical_typed_snapshot_sha256"]==digest(source)
    previous_names=set(BRIDGE_OUTCOME)|set(CLOSER_PAYABLE)|set(ASSIGNABLE);prior=previous["declarations"]
    assert len(prior)==len(previous_names)==36 and{r["theorem"]for r in prior}==previous_names
    assert previous["reviewed_role_records"]==len(prior)and not previous_names&set(SPECS)
    union=prior+records;assert len(union)==len({r["theorem"]for r in union})==44
    pending=[r for r in union if"pending_impossibility_certificate"in r];assert len(pending)==1 and pending[0]["accepted_H69"]is False
    payload={"frozen_assignment_base":BASE,"current_head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),"historical_typed_snapshot_sha256":digest(source),
      "declarations":records,"reviewed_role_records":len(records),"companion_report":str(companion),"companion_report_sha256":digest(companion),"companion_validation":dict(command=cmd,exit=x.returncode,decisive=x.stdout),
      "cumulative_original_roles":len(union),"remaining_original_roles":500-len(union),"joint_certificates_in_role_union":len(union)-len(pending),"ordinary_pending_impossibilities":len(pending),
      "new_joint_witnesses_added_by_inventory":0,"new_H69_dispositions":0,"generated_candidates_dispositioned":0,"full_assignment_acceptance":False,
      "boundary":"Eight selected Pure roles, no full Pure coverage. Historical frozen types plus byte-unchanged files/current proof receipts; no dependent-definition equivalence, termination of arbitrary loops, compiler target totality or gas guarantee."}
    (out/"pure-input-roles.json").write_text(json.dumps(payload,indent=2)+"\n")
    (out/"all-reviewed-pure-input-roles.json").write_text(json.dumps(dict(payload,declarations=union,reviewed_role_records=len(union),new_reviewed_role_records=len(records)),indent=2)+"\n")
    (out/"pure-original-dispositions.json").write_text(json.dumps(dict(frozen_assignment_base=BASE,explicit_declarations=26,declarations=dispositions,counts=counts,full_assignment_acceptance=False),indent=2)+"\n")
    print("PURE_INPUT_ROLES_PASS:8new roles;44disjoint originals;456rolespending;Pure8joint/17pending/1historicalempty;0newwitnesses;full_acceptance=false")
if __name__=="__main__":main()
