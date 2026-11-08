#!/usr/bin/env python3
"""Rehashed frozen-snapshot corruptions must fail the frozen tuple telescope pins; H69 classification is canonical.
External checks only; no Lean job and no added coverage or scope exclusion.
"""
import argparse,copy,fcntl,hashlib,json,os,subprocess,sys
from pathlib import Path
from census import ROOT
from run_frozen_history import LOCK

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ("historical-evidence","proof-evidence","out"):ap.add_argument("--"+name,type=Path,required=True)
    a=ap.parse_args();old=a.historical_evidence.resolve();proof=a.proof_evidence.resolve();out=a.out.resolve()
    if any(p.is_relative_to(ROOT) for p in (old,proof,out)) or out.exists():raise SystemExit("Use fresh off-Git control output")
    with LOCK.open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);out.mkdir(parents=True)
        original=json.loads((old/"verified-census.json").read_text());results=[]
        def execute(history,destination):
            command=[sys.executable,str(ROOT/"scripts/h62/item2/audit-theories/tuple_progress_input_roles.py"),"--historical-evidence",str(history),"--proof-evidence",str(proof),"--out",str(destination)]
            run=subprocess.run(command,env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1"),capture_output=True,text=True)
            return command,run
        command,run=execute(old,out/"positive");assert run.returncode==0,run.stderr
        (out/"positive.log").write_text(run.stdout+run.stderr);results.append(dict(case="positive",command=command,exit=0))
        for kind in ("duplicate-premise-dropped","duplicate-premise-aliased","lower-horizon-law-weakened","late-expression-dropped","post-fit-locals-dropped","tuple-kind-replaced","producer-route-replaced"):
            payload=copy.deepcopy(original)
            target=("Solidity.Theory.Progress.pushVals_ns" if kind.startswith("duplicate-") else "Solidity.Theory.Progress.Val.not_tuple" if kind=="tuple-kind-replaced" else "Solidity.Theory.Progress.declTuple_ns" if kind=="post-fit-locals-dropped" else "Solidity.Theory.Progress.argsFragment_le")
            row=next(r for r in payload["declarations"] if r["source_name"]==target);bs=row["elaborated"]["binders"]
            if kind.startswith("duplicate-"):
                assert bs[9]["name"]==bs[10]["name"] and bs[9]["is_prop"] and bs[10]["is_prop"] and bs[9]["type"]!=bs[10]["type"]
                if kind=="duplicate-premise-dropped":bs.pop(10)
                else:bs[10]["type"]=bs[9]["type"]
            elif kind=="lower-horizon-law-weakened":
                assert bs[6]["is_prop"];bs[6]["type"]="True"
            elif kind=="late-expression-dropped":
                assert bs[8]["name"]=="es" and bs[6]["is_prop"];bs.pop(8)
            elif kind=="post-fit-locals-dropped":
                assert bs[16]["name"]=="l" and bs[15]["is_prop"];bs.pop(16)
            elif kind=="tuple-kind-replaced":
                assert bs[2]["name"]=="v";bs[2]["type"]="RVal D (STy.tuple σs)"
            else:row["documented_producing_lane"]={"lane":"invented","evidence":"invented","live_confirmation":"confirmed"}
            case=out/kind;case.mkdir();raw=(json.dumps(payload,ensure_ascii=False,indent=2)+"\n").encode()
            (case/"verified-census.json").write_bytes(raw);(case/"SHA256SUMS").write_text(hashlib.sha256(raw).hexdigest()+"  verified-census.json\n")
            command,run=execute(case,case/"report");assert run.returncode==1 and "AssertionError" in run.stderr,(kind,run.returncode,run.stdout,run.stderr)
            expected=("Frozen source provenance changed" if kind=="producer-route-replaced" else "Frozen binder metadata changed")
            assert expected in run.stderr,run.stderr
            (case/"refusal.log").write_text(run.stdout+run.stderr)
            results.append(dict(case=kind,theorem=target,command=command,exit=run.returncode,snapshot_and_manifest_rehashed=True,snapshot_sha256=hashlib.sha256(raw).hexdigest()))
        # Forged historical coverage labels must never reclassify the impossible Val input.
        payload=copy.deepcopy(original);target="Solidity.Theory.Progress.Val.not_tuple"
        row=next(r for r in payload["declarations"] if r["source_name"]==target);row["status"]="joint-witness-checked"
        case=out/"H69-status-forged";case.mkdir();raw=(json.dumps(payload,ensure_ascii=False,indent=2)+"\n").encode()
        (case/"verified-census.json").write_bytes(raw);(case/"SHA256SUMS").write_text(hashlib.sha256(raw).hexdigest()+"  verified-census.json\n")
        command,run=execute(case,case/"report");assert run.returncode==0,run.stdout+run.stderr
        report=json.loads((case/"report/tuple-progress-input-roles.json").read_text());item=next(x for x in report["declarations"] if x["theorem"]==target)
        positive=json.loads((out/"positive/tuple-progress-input-roles.json").read_text());prior=next(x for x in positive["declarations"] if x["theorem"]==target)
        assert item["input_disposition"]=="intentional-H69-impossibility" and "designated_joint_certificate" not in item
        assert item["designated_impossibility_certificate"]==prior["designated_impossibility_certificate"] and report["ordinary_joint_records"]==5 and report["intentional_H69_records"]==1
        (case/"normalization.log").write_text(run.stdout+run.stderr);results.append(dict(case="H69-status-forged",theorem=target,command=command,exit=0,snapshot_and_manifest_rehashed=True,forged_joint_label_refused_by_canonical_derivation=True))
        (out/"controls.json").write_text(json.dumps(dict(cases=results,lean_jobs=0,full_assignment_acceptance=False),indent=2)+"\n")
    print("TUPLE_PROGRESS_ROLE_CONTROLS_PASS:positive+7rehashedrefusals+H69classification-normalized;no_Lean_jobs")
if __name__=="__main__":main()
