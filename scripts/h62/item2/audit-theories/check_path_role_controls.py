#!/usr/bin/env python3
"""Rehashed frozen-snapshot corruptions must fail the static path telescope pins.
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
            command=[sys.executable,str(ROOT/"scripts/h62/item2/audit-theories/path_input_roles.py"),"--historical-evidence",str(history),"--proof-evidence",str(proof),"--out",str(destination)]
            run=subprocess.run(command,env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1"),capture_output=True,text=True)
            return command,run
        command,run=execute(old,out/"positive");assert run.returncode==0,run.stderr
        (out/"positive.log").write_text(run.stdout+run.stderr);results.append(dict(case="positive",command=command,exit=0))
        for kind in ("late-replacement-dropped","universal-frame-weakened","type-expression-replaced","source-file-replaced","producer-route-replaced"):
            payload=copy.deepcopy(original)
            target="Solidity.SVal.saveM_of_findM" if kind=="late-replacement-dropped" else "Solidity.Obs.find_save_frame"
            row=next(r for r in payload["declarations"] if r["source_name"]==target)
            if kind=="late-replacement-dropped":
                assert row["elaborated"]["binders"][-1]["name"]=="v";row["elaborated"]["binders"].pop()
            elif kind=="universal-frame-weakened":
                premise=next(b for b in row["elaborated"]["binders"] if b["name"]=="h");assert premise["is_prop"];premise["type"]="True"
            elif kind=="source-file-replaced":row["file"]="Solidity/Theory/NotTheAuditedFile.lean"
            elif kind=="producer-route-replaced":row["documented_producing_lane"]={"lane":"invented","evidence":"invented","live_confirmation":"confirmed"}
            else:
                row["elaborated"]["type_expr"]="True";row["elaborated_type_sha256"]=hashlib.sha256(b"True").hexdigest()
            case=out/kind;case.mkdir();raw=(json.dumps(payload,ensure_ascii=False,indent=2)+"\n").encode()
            (case/"verified-census.json").write_bytes(raw);(case/"SHA256SUMS").write_text(hashlib.sha256(raw).hexdigest()+"  verified-census.json\n")
            command,run=execute(case,case/"report");assert run.returncode==1 and "AssertionError" in run.stderr,(kind,run.returncode,run.stdout,run.stderr)
            if kind in ("late-replacement-dropped","universal-frame-weakened"):assert "Frozen binder metadata changed" in run.stderr,run.stderr
            if kind in ("source-file-replaced","producer-route-replaced"):assert "Frozen source provenance changed" in run.stderr,run.stderr
            (case/"refusal.log").write_text(run.stdout+run.stderr)
            results.append(dict(case=kind,theorem=target,command=command,exit=run.returncode,snapshot_and_manifest_rehashed=True,snapshot_sha256=hashlib.sha256(raw).hexdigest()))
        (out/"controls.json").write_text(json.dumps(dict(cases=results,lean_jobs=0,full_assignment_acceptance=False),indent=2)+"\n")
    print("PATH_ROLE_CONTROLS_PASS:positive+5rehashedrefusals;no_Lean_jobs")
if __name__=="__main__":main()
