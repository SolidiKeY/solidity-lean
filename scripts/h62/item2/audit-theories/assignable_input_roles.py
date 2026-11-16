#!/usr/bin/env python3
"""Review all eight Assignable input telescopes and the authenticated36-role union.
Companion generators are rerun without Lean before deriving cumulative counts.
This inventory adds no witnesses and accepts no pending impossible interface.
"""
import argparse,json,os,subprocess,sys
from pathlib import Path
from census import ROOT,BASE,scan
from input_roles import annotate,digest,SPECS as BRIDGE_OUTCOME
from mutability_input_roles import SPECS as CLOSER_PAYABLE
import verify_census as v
SPECS={}
def add(name,binders,config,premises,notes):
    SPECS["Solidity.Theory.Mutability."+name]={"binders":binders.split(),"configuration":config.split(),"premises":premises,"notes":notes}
add("Frames.nothing","C Γ Δ σ τ h U r","C Γ Δ",{"h":"per-state-pair-universal-root-frame"},
    "Frames quantifies every typed root outside the selected clause for THIS state pair; it is not a global all-states assumption. Late U/r remain inputs. A populated contract and real primitive root prevent an empty root domain.")
add("Frames.mono","C Γ Δ L M hLM σ τ h","C Γ Δ",{"hLM":"per-clause-pair-universal-inclusion","h":"per-state-pair-universal-root-frame"},
    "Subset is universal over members of selected L, not every clause pair. Packet uses nonempty proper inclusion and Frames for the SAME populated states. Neither premise is replaced by individual inhabitance.")
add("Frames.of_globals","C Γ Δ L σ τ h","C Γ Δ",{"h":"per-state-pair-complete-globals-equality"},
    "Globals equality concerns selected compatible states only. The concrete equal-state pair establishes feasibility, not independence of every arbitrary pair or compiler execution.")
for name,binders in [("Prog.frames_readOnly","C μ Γ Γ' P hw hμ L σ o h"),("Prog.storage_readOnly","C μ Γ Γ' P hw hμ σ o h U r")]:
    add(name,binders,"C Γ Γ'",{"hw":"per-program-mutability-check","hμ":"per-input-mutability-restriction","h":"per-input-actual-success-equation"},
      "Selected mutability/program/state/output must coexist. within is not a global premise structure; actual .ok equation supplies one successful run. All late clause/state/output/root/type binders are retained. Packet uses a nonempty local declaration with populated storage.")
add("Prog.frames_of_storeAt","C Γ Γ' P M L hs hML σ o h","C Γ Γ'",{"hs":"per-program-modifies-equation","hML":"per-modifies-clause-universal-inclusion","h":"per-input-actual-success-equation"},
    "Modifies set and universal inclusion apply to this P/M/L, not all programs. Packet writes the real flag root with M=[flag], rather than meeting inclusion over an empty set. Output and actual success refer to the same write.")
add("assignableCheck_sound","C Γ Γ' P locs hc σ o h","C Γ Γ'",{"hc":"per-program-clause-check-success","h":"per-input-actual-success-equation"},
    "Boolean check is for this typed program/clause. Packet succeeds through a nonempty modifies branch; within.view is false. Check acceptance alone is not execution totality, so actual success is separately correlated.")
add("committed_frames","C Γ Γ' P locs hc σ","C Γ Γ'",{"hc":"per-program-clause-check-success"},
    "No source-success premise in the original theorem: errors make its CommittedFrames conclusion True. Witness additionally proves real successful storage write; this support does not add an original premise or claim reject-all compiler exclusion by this statement alone.")
FILE="Solidity/Theory/Mutability/Assignable.lean"
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for n in ("out","proof-evidence","historical-evidence"):ap.add_argument("--"+n,type=Path,required=True)
    a=ap.parse_args();out=a.out.resolve();proof=a.proof_evidence.resolve();old=a.historical_evidence.resolve()
    if any(p.is_relative_to(ROOT)for p in(out,proof,old)):raise SystemExit("Use off-Git evidence")
    out.mkdir(parents=True,exist_ok=True);commands=[]
    for tool in ("input_roles.py","mutability_input_roles.py"):
        cmd=[sys.executable,str(Path(__file__).resolve().with_name(tool)),"--out",str(out),"--proof-evidence",str(proof),"--historical-evidence",str(old)]
        x=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1"))
        commands.append(dict(command=cmd,exit=x.returncode,decisive=x.stdout+x.stderr))
        assert x.returncode==0,(tool,x.stdout,x.stderr)
    source=old/"verified-census.json";manifest=dict((line.split("  ",1)[1],line.split("  ",1)[0])for line in(old/"SHA256SUMS").read_text().splitlines())
    assert digest(source)==manifest["verified-census.json"]
    historical=json.loads(source.read_text());assert historical["base"]==BASE
    frozen=subprocess.check_output(["git","show",BASE+":"+FILE],cwd=ROOT);assert(ROOT/FILE).read_bytes()==frozen
    selected={r["source_name"]:r for r in scan(frozen.decode(),FILE)};assert set(selected)==set(SPECS) and len(selected)==8
    originals={r["source_name"]:r for r in historical["declarations"]}
    v.VERSION=json.loads((proof/"serial/baseline-results.json").read_text())["version"];v.FINGERPRINTS.clear();v.checked_module(proof/"serial",FILE)
    records=[]
    for name,spec in SPECS.items():
        row=originals[name];assert row["source_header"]==selected[name]["source_header"]
        report=annotate(row,spec);report.update(status="joint-witness-checked",current_joint_certificate=v.certificate(proof/"serial",*v.WITNESSES[name]));records.append(report)
    paths=[out/"input-roles.json",out/"mutability-input-roles.json"];previous=[]
    for path,expected in zip(paths,(BRIDGE_OUTCOME,CLOSER_PAYABLE)):
        payload=json.loads(path.read_text());assert payload["frozen_assignment_base"]==BASE and payload["historical_typed_snapshot_sha256"]==digest(source)
        rows=payload["declarations"];assert len(rows)==len(expected) and {r["theorem"]for r in rows}==set(expected)
        previous.extend(rows)
    union=previous+records;names=[r["theorem"]for r in union];assert len(names)==len(set(names))==36
    pending=[r for r in union if "pending_impossibility_certificate"in r];assert not pending
    intentional=[r for r in union if "current_impossibility_certificate"in r];assert len(intentional)==1 and intentional[0]["accepted_H69"]is True
    payload={"frozen_assignment_base":BASE,"current_head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),"historical_typed_snapshot_sha256":digest(source),
      "declarations":records,"reviewed_role_records":len(records),"companion_reports":{str(p):digest(p)for p in paths},"companion_validation_commands":commands,
      "cumulative_original_roles":len(union),"remaining_original_roles":500-len(union),"joint_certificates_in_role_union":len(union)-len(pending)-len(intentional),"accepted_H69_in_role_union":len(intentional),"ordinary_pending_impossibilities":len(pending),
      "new_joint_witnesses_added_by_inventory":0,"new_H69_dispositions":0,"generated_candidates_dispositioned":0,"full_assignment_acceptance":False,
      "boundary":"Frozen historical typed signatures, byte-unchanged selected files, current proof receipts; no equivalence for changed definitions elsewhere or target compiler totality."}
    (out/"assignable-input-roles.json").write_text(json.dumps(payload,indent=2)+"\n")
    (out/"all-reviewed-input-roles.json").write_text(json.dumps(dict(payload,declarations=union,reviewed_role_records=len(union),new_reviewed_role_records=len(records)),indent=2)+"\n")
    print("ASSIGNABLE_INPUT_ROLES_PASS:8new records;36checked disjoint originals;464rolespending;0newwitnesses;full_acceptance=false")
if __name__=="__main__":main()
