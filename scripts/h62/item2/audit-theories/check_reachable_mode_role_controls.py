#!/usr/bin/env python3
"""Rehashed frozen-snapshot corruptions must fail the occurrence-based reachable-mode telescope pins.
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
            command=[sys.executable,str(ROOT/"scripts/h62/item2/audit-theories/reachable_mode_input_roles.py"),"--historical-evidence",str(history),"--proof-evidence",str(proof),"--out",str(destination)]
            run=subprocess.run(command,env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1"),capture_output=True,text=True)
            return command,run
        command,run=execute(old,out/"positive");assert run.returncode==0,run.stderr
        (out/"positive.log").write_text(run.stdout+run.stderr);results.append(dict(case="positive",command=command,exit=0))
        for kind in ("entry-law-weakened","calls-law-weakened","predicate-data-reclassified","late-state-dropped","private-identity-publicized","producer-route-replaced"):
            payload=copy.deepcopy(original)
            target=("Solidity.Reachable.reset_ofState" if kind=="private-identity-publicized" else "Solidity.Reachable.ValidStart.of_invariant" if kind in ("entry-law-weakened","predicate-data-reclassified") else "Solidity.Reachable.PersistentFml.invariant" if kind=="calls-law-weakened" else "Solidity.Reachable.EntryState.invariant")
            row=next(r for r in payload["declarations"] if r["source_name"]==target);bs=row["elaborated"]["binders"]
            if kind in ("entry-law-weakened","calls-law-weakened"):
                premise=next(b for b in bs if b["name"]==("entry" if kind=="entry-law-weakened" else "calls"));assert premise["is_prop"];premise["type"]="True"
            elif kind=="predicate-data-reclassified":
                assert bs[4]["name"]=="I" and not bs[4]["is_prop"];bs[4]["is_prop"]=True
            elif kind=="late-state-dropped":
                assert bs[6]["name"]=="σ" and bs[5]["is_prop"];bs.pop(6)
            elif kind=="private-identity-publicized":
                assert row["visibility"]=="private" and row["elaborated"]["name"]!=target;row["elaborated"]["name"]=target
            else:row["documented_producing_lane"]={"lane":"invented","evidence":"invented","live_confirmation":"confirmed"}
            case=out/kind;case.mkdir();raw=(json.dumps(payload,ensure_ascii=False,indent=2)+"\n").encode()
            (case/"verified-census.json").write_bytes(raw);(case/"SHA256SUMS").write_text(hashlib.sha256(raw).hexdigest()+"  verified-census.json\n")
            command,run=execute(case,case/"report");assert run.returncode==1 and "AssertionError" in run.stderr,(kind,run.returncode,run.stdout,run.stderr)
            expected=("Frozen elaborated identity changed" if kind=="private-identity-publicized" else "Frozen source provenance changed" if kind=="producer-route-replaced" else "Frozen binder metadata changed")
            assert expected in run.stderr,run.stderr
            (case/"refusal.log").write_text(run.stdout+run.stderr)
            results.append(dict(case=kind,theorem=target,command=command,exit=run.returncode,snapshot_and_manifest_rehashed=True,snapshot_sha256=hashlib.sha256(raw).hexdigest()))
        (out/"controls.json").write_text(json.dumps(dict(cases=results,lean_jobs=0,full_assignment_acceptance=False),indent=2)+"\n")
    print("REACHABLE_MODE_ROLE_CONTROLS_PASS:positive+6rehashedrefusals;no_Lean_jobs")
if __name__=="__main__":main()
