#!/usr/bin/env python3
"""Account for every ORIGINAL frozen declaration/candidate after rebaselining.
This ledger retains historical signatures and checks current proof certificates;
it never promotes changed-file/version fidelity to full acceptance. All original
generated candidates remain pending. Bulk output stays outside Git.
"""
import argparse,hashlib,json,subprocess
from collections import Counter
from pathlib import Path
from census import ROOT,BASE
import verify_census as verification
from pending_impossibility import PENDING

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--proof-evidence",type=Path,required=True)
    ap.add_argument("--historical-evidence",type=Path,required=True)
    a=ap.parse_args();out=a.out.resolve();proof=a.proof_evidence.resolve();old=a.historical_evidence.resolve()
    if any(p.is_relative_to(ROOT)for p in (out,proof,old)):raise SystemExit("Use off-Git evidence")
    manifest={line.split("  ",1)[1]:line.split("  ",1)[0]for line in (old/"SHA256SUMS").read_text().splitlines()}
    historical=old/"verified-census.json";assert sha(historical)==manifest[historical.name]
    previous=json.loads(historical.read_text());assert previous["base"]==BASE
    verification.VERSION=json.loads((proof/"serial/baseline-results.json").read_text())["version"]
    verification.FINGERPRINTS.clear()
    originals=previous["declarations"];generated=previous["generated_candidates"]
    assert len(originals)==500 and len(generated)==986
    names={r["source_name"]for r in originals};assert len(names)==500
    assert set(verification.WITNESSES)<=names and set(verification.IMPOSSIBLE)<=names
    assert not set(verification.WITNESSES)&set(verification.IMPOSSIBLE)
    assert {r["source_name"]for r in originals if r["status"]=="joint-witness-checked"}<=set(verification.WITNESSES)
    file_status={}
    for file in {r["file"]for r in originals}:
        frozen=subprocess.check_output(["git","show",BASE+":"+file],cwd=ROOT)
        file_status[file]="byte-unchanged" if (ROOT/file).read_bytes()==frozen else "changed-frozen-file-version-pending"
    rows=[];gaps=[]
    for oldrow in originals:
        row={k:oldrow[k]for k in ("source_name","file","line","visibility","source_header","elaborated_type_sha256","documented_producing_lane","proving_owner")}
        name=row["source_name"];row["signature_source"]="historical original frozen typed census"
        row["frozen_file_status"]=file_status[row["file"]]
        if name in verification.WITNESSES:
            row["status"]="joint-certificate-present-version-fidelity-separate"
            row["current_certificate"]=verification.certificate(proof/"serial",*verification.WITNESSES[name])
        elif name in verification.IMPOSSIBLE:
            row["status"]="H69-intentional-impossibility-certificate-present"
            row["current_certificate"]=verification.certificate(proof/"serial",*verification.IMPOSSIBLE[name])
            row["intentional_reason"]=verification.INTENTIONAL_REASONS[name]
        elif oldrow["status"]=="no-inputs":row["status"]="historical-empty-input-telescope"
        else:
            row["status"]="private-witness-pending" if row["visibility"]=="private"else "public-witness-pending"
            if name in PENDING:
                item=PENDING[name]
                assert name not in verification.IMPOSSIBLE and name not in verification.WITNESSES
                row["pending_joint_impossibility"]={"certificate":verification.certificate(proof/"serial",item["module"],item["helper"]),"question":item["question"],"reason":item["reason"],"accepted_H69":False}
            gaps.append({"theorem":oldrow["elaborated"]["name"],"source_name":name,
              "file":row["file"],"line":row["line"],"status":row["status"],
              "documented_producing_lane":row["documented_producing_lane"],"proving_owner":row["proving_owner"]})
        rows.append(row)
    for candidate in generated:
        gaps.append({"theorem":candidate["name"],"source_name":None,"file":candidate["file"],"line":None,
          "status":"original-generated-candidate-pending","documented_producing_lane":candidate["documented_producing_lane"],"proving_owner":candidate["proving_owner"]})
    assert len(rows)==500 and len({r["source_name"]for r in rows})==500
    assert len(gaps)==len({r["theorem"]for r in gaps}),"Duplicate original remaining record"
    counts=dict(Counter(r["status"]for r in rows))
    payload={"frozen_assignment_base":BASE,"current_head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),
      "historical_typed_snapshot_sha256":sha(historical),"original_explicit_counts":counts,
      "original_explicit_declarations":rows,"original_generated_candidates_pending":len(generated),
      "current_generated_inventory":"Not refreshed; original986 candidates retained without exclusion.",
      "remaining_original_records":len(gaps),"pending_impossibility_questions":[dict(theorem=n,question=i["question"],accepted_H69=False)for n,i in PENDING.items()],"changed_frozen_files":sorted(f for f,s in file_status.items()if s!="byte-unchanged"),
      "version_fidelity_boundary":"Current joint proof receipts and historical signature accounting are separate. No equivalence claim for changed files or definitions; original full census remains fail-closed pending Q-FROZEN-REBASE.","full_assignment_acceptance":False}
    out.mkdir(parents=True,exist_ok=True)
    (out/"original-coverage-ledger.json").write_text(json.dumps(payload,indent=2)+"\n")
    (out/"remaining-original-records.json").write_text(json.dumps(gaps,indent=2)+"\n")
    print("ORIGINAL_COVERAGE_LEDGER_PASS "+json.dumps({"explicit":500,"counts":counts,"generated_pending":len(generated),"remaining":len(gaps),"full_assignment_acceptance":False}))

if __name__=="__main__":main()
