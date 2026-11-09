#!/usr/bin/env python3
"""Ordered premise-role audit for all11 original Closer/Payable interfaces.
Adds no witnesses. Explicit coordinator Q-STATIC-VALUE classifies the static
packet as an intentional H69 boundary, without operational refusal coverage.
"""
import argparse,json,subprocess
from pathlib import Path
from census import ROOT,BASE,scan
from input_roles import annotate,digest,SPECS as PREVIOUS_SPECS
import verify_census as v
from pending_impossibility import PENDING
from audit_dispositions import ACCEPTED,accepted_fields

SPECS={}
def add(name,binders,config,premises,notes):
    SPECS["Solidity.Theory.Mutability."+name]={"binders":binders.split(),"configuration":config.split(),"premises":premises,"notes":notes}
add("refuses","payable v hp hv","",{"hp":"per-input-entry-flag","hv":"per-input-nonzero-integer"},
    "Both logical hypotheses concern the same flag and arbitrary integer, which may be negative. They are jointly inhabited, not separate inhabited propositions.")
add("System.run_nonpayable","C D A M s a tx hp hv","C D A M",{"hp":"per-input-entry-flag","hv":"per-input-positive-value"},
    "System contains callable data but no universal success guarantee. The flag premise concerns selected a, not every action; s and tx are correlated per-input values. A separate payable-positive model run succeeds.")
add("deployT_nonpayable","C Γ' P tx hp hv","C Γ'",{"hp":"configuration-selected-constructor-flag","hv":"per-input-positive-value"},
    "The constructor flag is selected from C. P is an intrinsically typed program and tx is per-input; constructor metadata alone is not deployment admission or target success.")
add("transact_nonpayable","C L α body world tx ctx hv","C L α",{"hv":"per-input-positive-value"},
    "Transient layout and body/world/transaction/context coexist. Nonempty read layout is witnessed; the refusal occurs before a run, and does not demonstrate a successful transient execution by itself.")
add("ContractWorld.World.enter_nonpayable","K contracts w k self ctx st hv","K contracts",{"hv":"per-input-positive-value"},
    "World data is not a universal feasibility premise. Selected k/storage/address/context are coherent; fixture additionally has installed matching code and funds. Positive payable entry is a separate control.")
add("ContractWorld.World.enter_static","K contracts w k self ctx st payable hs hv","K contracts",{"hs":"per-input-static-mode","hv":"per-input-positive-value"},
    "The SAME Context cannot be static and have nonzero value under frozen Mode. Full telescope is refuted. Coordinator Q-STATIC-VALUE option3 accepts this intentional H69 separation boundary; no operational refusal coverage or interface repair.")
# Keep the full historical instance name: a typeclass binder is still an input.
EQ="inst._@.Solidity.Theory.Mutability.Payable.2820293433._hygCtx._hyg.4"
add("ContractWorld.World.callFrame_nonpayable",f"K {EQ} contracts w k α r entry ctx hp hv","K contracts α",{"hp":"per-input-entry-flag","hv":"per-input-positive-value"},
    "DecidableEq K is a global equality-operation instance, not a proof that any call is feasible. Handle/entry/context refer to one correlated call. Installed matching code/funds are supplied by the packet; separate sender!=self payable call succeeds through settlement.")
for name,binders,config,post in [
 ("holds_modal_readOnly","C μ m Γ Γ' P hw hμ σ φ hφ o h","C Γ Γ'","per-input-modal-postcondition"),
 ("Spec.box_readOnly","C μ Γ Γ' P hw hμ σ φ hφ o h","C Γ Γ'","per-input-spec-postcondition")]:
    add(name,binders,config,{"hw":"per-program-mutability-check","hμ":"per-input-mutability-restriction","hφ":post,"h":"per-input-actual-success-equation"},
      "within is a selected-program check, not a global inhabited premise structure. Formula/spec and modal fact refer to THIS state/program; o and success h occur after earlier premises and remain explicit inputs. The nonempty bool declaration actually succeeds; a modal failure alone is not counted.")
add("Transient.holds_readOnly","C L α m body post ctx s hμ proved","C L α",{"hμ":"per-input-readonly-context","proved":"per-input-modal-postcondition"},
    "The post callback is correlated data, not a universally valid program law. Holds quantifies the selected body's outcome. Actual read success with a populated bool cell supplements its joint packet. ReadOnlyCtx is an OR, not two independent global assumptions.")
add("Transient.holds_frame","C L α body ctx s hμ noPanic","C L α",{"hμ":"per-input-readonly-context","noPanic":"per-input-panic-exclusion"},
    "noPanic excludes one selected run's panic; it is not a forall-program totality law. Packet also gives actual read success, so a mere nonpanic revert does not substitute for meaningful success. Context/body/frame are jointly typed.")

FILES=["Solidity/Theory/Mutability/Closer.lean","Solidity/Theory/Mutability/Payable.lean"]
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for n in ("out","proof-evidence","historical-evidence"):ap.add_argument("--"+n,type=Path,required=True)
    a=ap.parse_args();out=a.out.resolve();proof=a.proof_evidence.resolve();old=a.historical_evidence.resolve()
    if any(p.is_relative_to(ROOT) for p in (out,proof,old)):raise SystemExit("Use off-Git evidence")
    source=old/"verified-census.json";manifest=dict((line.split("  ",1)[1],line.split("  ",1)[0])for line in(old/"SHA256SUMS").read_text().splitlines())
    assert digest(source)==manifest["verified-census.json"]
    historical=json.loads(source.read_text());assert historical["base"]==BASE
    selected={}
    for f in FILES:
        frozen=subprocess.check_output(["git","show",BASE+":"+f],cwd=ROOT)
        assert (ROOT/f).read_bytes()==frozen,"Frozen interface file changed"
        selected.update({r["source_name"]:r for r in scan(frozen.decode(),f)})
    assert set(selected)==set(SPECS) and len(selected)==11
    v.VERSION=json.loads((proof/"serial/baseline-results.json").read_text())["version"];v.FINGERPRINTS.clear()
    for f in FILES:v.checked_module(proof/"serial",f)
    originals={r["source_name"]:r for r in historical["declarations"]};records=[]
    for name,spec in SPECS.items():
        row=originals[name];assert row["source_header"]==selected[name]["source_header"]
        report=annotate(row,spec)
        if name in PENDING:
            item=PENDING[name];assert name not in v.WITNESSES and name not in v.IMPOSSIBLE
            report.update(status=item["status"],question=item["question"],accepted_H69=False,
              pending_impossibility_certificate=v.certificate(proof/"serial",item["module"],item["helper"]))
        elif name in ACCEPTED:
            item=ACCEPTED[name];assert name in v.IMPOSSIBLE and name not in v.WITNESSES
            report.update(**accepted_fields(name),current_impossibility_certificate=v.certificate(proof/"serial",item["module"],item["helper"]))
        else:
            report.update(status="joint-witness-checked",current_joint_certificate=v.certificate(proof/"serial",*v.WITNESSES[name]))
        for b in report["binders"]:
            if b["name"]==EQ:b["role"]="global-equality-operation-instance-data"
        records.append(report)
    assert sum(r["status"]=="joint-witness-checked" for r in records)==10
    previous_path=out/"input-roles.json"
    previous=json.loads(previous_path.read_text())
    assert previous["frozen_assignment_base"]==BASE and previous["historical_typed_snapshot_sha256"]==digest(source)
    prior=previous["declarations"];assert len(prior)==len(PREVIOUS_SPECS)==17
    assert {r["theorem"]for r in prior}==set(PREVIOUS_SPECS)
    for report in prior:
        name=report["theorem"];expected=annotate(originals[name],PREVIOUS_SPECS[name])
        frozen=originals[name]["file"]
        assert (ROOT/frozen).read_bytes()==subprocess.check_output(["git","show",BASE+":"+frozen],cwd=ROOT)
        expected["current_joint_certificate"]=v.certificate(proof/"serial",*v.WITNESSES[name])
        assert report==expected,"Previous role record/provenance mismatch"
    assert set(SPECS).isdisjoint(PREVIOUS_SPECS)
    cumulative=len(records)+len(prior);assert cumulative==28
    payload={"frozen_assignment_base":BASE,"current_head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),
      "historical_typed_snapshot_sha256":digest(source),"declarations":records,"reviewed_role_records":11,
      "previous_disjoint_Bridge_Outcome_roles":len(prior),"previous_role_report_sha256":digest(previous_path),"cumulative_original_roles":cumulative,"remaining_original_roles":500-cumulative,
      "joint_certificates":10,"ordinary_pending_impossibility":0,"accepted_H69_dispositions":1,"new_H69_dispositions":0,
      "new_joint_witnesses_added_by_inventory":0,"generated_candidates_dispositioned":0,"full_assignment_acceptance":False,
      "boundary":"Historical frozen types plus byte-unchanged current files and current proof receipts; no whole-tree dependent-definition fidelity or compiler totality claim."}
    out.mkdir(parents=True,exist_ok=True);(out/"mutability-input-roles.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("MUTABILITY_INPUT_ROLES_PASS:11ordered records,10joint+1explicit-H69,28cumulative roles;full_acceptance=false")
if __name__=="__main__":main()
