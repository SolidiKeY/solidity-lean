#!/usr/bin/env python3
"""Acceptance controls for explicit H69/history decisions; no Lean/source edits."""
import argparse,json,subprocess,sys
from pathlib import Path
from census import ROOT
STATIC="Solidity.Theory.Mutability.ContractWorld.World.enter_static"
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for n in("evidence","roles","historical-evidence","out"):ap.add_argument("--"+n,type=Path,required=True)
    a=ap.parse_args();proof=a.evidence.resolve();role=a.roles.resolve();old=a.historical_evidence.resolve();out=a.out.resolve()
    if any(p.is_relative_to(ROOT)for p in(proof,role,old,out)):raise SystemExit("Use off-Git evidence")
    out.mkdir(parents=True,exist_ok=True);tool=Path(__file__).resolve().with_name("verify_acceptance_snapshot.py")
    def run(pr,rf,d):
        cmd=[sys.executable,str(tool),"--evidence",str(pr),"--roles",str(rf),"--historical-evidence",str(old),"--out",str(d)]
        x=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True);log=d/"result.log";log.write_text(x.stdout+x.stderr)
        return x,dict(command=cmd,exit=x.returncode,log=str(log))
    x,positive=run(proof,role,out);assert x.returncode==0,(x.stdout,x.stderr)
    controls=[]
    for case in("H69-promoted-to-joint","operational-refusal-claim","decision-sha-altered","ordinary-Pure-promoted-to-H69","role-count-mismatch","history-replaced-by-equivalence","remaining-owner-altered"):
        d=out/case;d.mkdir(exist_ok=True);roles=json.loads(role.read_text());static=next(r for r in roles["declarations"]if r["theorem"]==STATIC);pr=proof
        if case=="H69-promoted-to-joint":static["status"]="joint-witness-checked";static["current_joint_certificate"]=static["current_impossibility_certificate"];marker="Accepted H69 role metadata mismatch"
        elif case=="operational-refusal-claim":static["operational_refusal_coverage"]=True;marker="Accepted H69 role metadata mismatch"
        elif case=="decision-sha-altered":static["decision_sha256"]="0"*64;marker="Accepted H69 role metadata mismatch"
        elif case=="ordinary-Pure-promoted-to-H69":
            row=next(r for r in roles["declarations"]if r["theorem"]=="Solidity.Theory.Mutability.TLoop.run_map");row["accepted_H69"]=True;row["status"]=static["status"];marker="Joint role status mismatch"
        elif case=="role-count-mismatch":roles["reviewed_role_records"]=8;marker="Role declaration/count mismatch"
        else:
            pr=d/"proof";pr.mkdir(exist_ok=True)
            for n in("serial","original-coverage-ledger.json","verified-helpers.json","remaining-original-records.json"):
                if n==("original-coverage-ledger.json"if case=="history-replaced-by-equivalence"else"remaining-original-records.json"):continue
                if not(pr/n).exists():(pr/n).symlink_to(proof/n,target_is_directory=n=="serial")
            if case=="history-replaced-by-equivalence":
                obj=json.loads((proof/"original-coverage-ledger.json").read_text());obj["fidelity_disposition"]["status"]="original-and-rebased-statements-equivalent";(pr/"original-coverage-ledger.json").write_text(json.dumps(obj)+"\n");marker="AssertionError"
            else:
                obj=json.loads((proof/"remaining-original-records.json").read_text());obj[0]["proving_owner"]="corrupted-control-owner";(pr/"remaining-original-records.json").write_text(json.dumps(obj)+"\n");marker="Remaining record metadata/owner mismatch"
        rf=d/"roles.json";rf.write_text(json.dumps(roles)+"\n");x,row=run(pr,rf,d)
        assert x.returncode!=0 and marker in x.stderr and not(d/"acceptance-snapshot.json").exists(),(case,x.stdout,x.stderr)
        controls.append(dict(row,case=case,expected_refusal=marker))
    (out/"disposition-controls.json").write_text(json.dumps(dict(positive=positive,negative_controls=controls,lean_jobs=0),indent=2)+"\n")
    print("DISPOSITION_CONTROLS_PASS:positive+7refusals;H69notjoint,nooperationalclaim,historynot-equivalence;lean_jobs=0")
if __name__=="__main__":main()
