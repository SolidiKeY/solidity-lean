#!/usr/bin/env python3
"""Rehashed frozen-snapshot corruptions must fail the frozen leaf-extension telescope pins.
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
            command=[sys.executable,str(ROOT/"scripts/h62/item2/audit-theories/leaf_progress_input_roles.py"),"--historical-evidence",str(history),"--proof-evidence",str(proof),"--out",str(destination)]
            run=subprocess.run(command,env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1"),capture_output=True,text=True)
            return command,run
        command,run=execute(old,out/"positive");assert run.returncode==0,run.stderr
        (out/"positive.log").write_text(run.stdout+run.stderr);results.append(dict(case="positive",command=command,exit=0))
        for kind in ("global-law-weakened","horizon-law-specialized","predicate-data-reclassified","global-program-dropped","full-type-replaced","producer-route-replaced"):
            payload=copy.deepcopy(original)
            target="Solidity.Theory.Progress.builtinExt_sound"
            row=next(r for r in payload["declarations"] if r["source_name"]==target);bs=row["elaborated"]["binders"]
            assert [b["name"] for b in bs]==["E","G","A","Q","hAll"]
            if kind=="global-law-weakened":
                assert bs[4]["is_prop"];bs[4]["type"]="True"
            elif kind=="horizon-law-specialized":
                bs[4]["type"]="∀ F, Q F.contract → ExprNSAt A G F 8"
            elif kind=="predicate-data-reclassified":
                assert not bs[3]["is_prop"];bs[3]["is_prop"]=True
            elif kind=="global-program-dropped":bs.pop(1)
            elif kind=="full-type-replaced":
                row["elaborated"]["type_expr"]="Lean.Expr.const `True []"
                row["elaborated_type_sha256"]=hashlib.sha256(row["elaborated"]["type_expr"].encode()).hexdigest()
            else:row["documented_producing_lane"]={"lane":"invented","evidence":"invented","live_confirmation":"confirmed"}
            case=out/kind;case.mkdir();raw=(json.dumps(payload,ensure_ascii=False,indent=2)+"\n").encode()
            (case/"verified-census.json").write_bytes(raw);(case/"SHA256SUMS").write_text(hashlib.sha256(raw).hexdigest()+"  verified-census.json\n")
            command,run=execute(case,case/"report");assert run.returncode==1 and "AssertionError" in run.stderr,(kind,run.returncode,run.stdout,run.stderr)
            expected=("Frozen elaborated type changed" if kind=="full-type-replaced" else "Frozen source provenance changed" if kind=="producer-route-replaced" else "Frozen binder metadata changed")
            assert expected in run.stderr,run.stderr
            (case/"refusal.log").write_text(run.stdout+run.stderr)
            results.append(dict(case=kind,theorem=target,command=command,exit=run.returncode,snapshot_and_manifest_rehashed=True,snapshot_sha256=hashlib.sha256(raw).hexdigest()))
        (out/"controls.json").write_text(json.dumps(dict(cases=results,lean_jobs=0,full_assignment_acceptance=False),indent=2)+"\n")
    print("LEAF_PROGRESS_ROLE_CONTROLS_PASS:positive+6rehashedrefusals;no_Lean_jobs")
if __name__=="__main__":main()
