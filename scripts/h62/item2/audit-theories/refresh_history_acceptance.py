#!/usr/bin/env python3
"""Refresh derived frozen-history accounting without copying stale reports.
Only immutable proof/census inputs are linked; every report is regenerated.
Receipt validation is external and does not rerun Lean or complete the goal.
"""
import argparse,fcntl,hashlib,json,os,subprocess
from pathlib import Path
from census import ROOT,BASE
from run_frozen_history import LOCK
INPUTS=("serial","census","census-output-receipt.json","census-replay.json","elaborated.json","elaborated-replay.json")
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ("proof-evidence","historical-evidence","out"):ap.add_argument("--"+name,type=Path,required=True)
    a=ap.parse_args();proof=a.proof_evidence.resolve();old=a.historical_evidence.resolve();out=a.out.resolve()
    if any(p.is_relative_to(ROOT) for p in (proof,old,out)) or out.exists() or out.is_relative_to(proof) or out.is_relative_to(old):raise SystemExit("Use fresh off-Git output outside inputs")
    assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()==BASE,"Use exact frozen validation overlay"
    with LOCK.open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);out.mkdir(parents=True);rows=[]
        for name in INPUTS:
            source=proof/name;assert source.exists(),source;(out/name).symlink_to(source,target_is_directory=source.is_dir())
        def run(name,args):
            cmd=[str(x) for x in ["python3",Path(__file__).resolve().with_name(name+".py"),*args]];log=out/(name+".log")
            with log.open("w") as stream:r=subprocess.run(cmd,cwd=ROOT,env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1"),stdout=stream,stderr=subprocess.STDOUT)
            rows.append(dict(command=cmd,cwd=str(ROOT),exit=r.returncode,log=str(log)));(out/"refresh-gates.json").write_text(json.dumps(rows,indent=2)+"\n");r.check_returncode()
        run("verify_census",["--evidence",out,"--require-complete-explicit-module","Solidity/Theory/Reachable/CleanTail.lean"])
        run("verify_helpers",["--evidence",out])
        common=["--out",out,"--proof-evidence",out,"--historical-evidence",old]
        run("coverage_ledger",common)
        run("pure_input_roles",common)
        run("verify_acceptance_snapshot",["--evidence",out,"--roles",out/"all-reviewed-pure-input-roles.json","--historical-evidence",old,"--out",out])
        run("verify_payable",["--evidence",out,"--require-ordinary-complete"])
        run("verify_totality",["--evidence",out])
        for name in ("path_input_roles","mirror_input_roles","clean_tail_input_roles"):run(name,common)
        ledger=json.loads((out/"original-coverage-ledger.json").read_text());snapshot=json.loads((out/"acceptance-snapshot.json").read_text());helpers=json.loads((out/"verified-helpers.json").read_text())
        assert snapshot["joint_certificates"]==109 and snapshot["accepted_H69"]==4 and snapshot["remaining_original_records"]==1355
        assert helpers["proved_theorems"]==snapshot["checked_helper_theorems"]==163
        assert snapshot["reviewed_roles"]==44 and snapshot["remaining_roles"]==456
        assert ledger["remaining_original_records"]==len(json.loads((out/"remaining-original-records.json").read_text()))==1355
        groups=[json.loads((out/name).read_text())["declarations"] for name in ("all-reviewed-pure-input-roles.json","path-input-roles.json","mirror-input-roles.json","clean-tail-input-roles.json")]
        names=[r["theorem"] for group in groups for r in group];assert len(names)==len(set(names))==104
        summary=dict(frozen_base=BASE,helpers=163,joint=109,H69=4,remaining_original_records=1355,legacy_acceptance_roles=44,separate_disjoint_role_records=104,remaining_role_specifications=396,lean_jobs=0,full_assignment_acceptance=False,boundary="All104 role records validated in separate reports on original history; legacy acceptance snapshot remains44, no merged104 acceptance or physical compiler claim.")
        (out/"refresh-summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    print("HISTORY_ACCEPTANCE_REFRESH_PASS:163helpers;109joint;1355pending;legacy44;separate104;no_Lean_jobs")
if __name__=="__main__":main()
