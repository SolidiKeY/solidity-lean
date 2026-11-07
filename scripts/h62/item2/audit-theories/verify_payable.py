#!/usr/bin/env python3
"""Account all seven unchanged Payable interfaces without accepting a vacuous one.
Six joint packets, one pending checked impossibility and three positive API
controls remain distinctly reported. --require-joint-all MUST fail while pending.
"""
import argparse,json,subprocess
from pathlib import Path
from census import ROOT,BASE,scan
import verify_census as v
from pending_impossibility import PENDING
FILE="Solidity/Theory/Mutability/Payable.lean"

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--evidence",required=True,type=Path)
    ap.add_argument("--require-joint-all",action="store_true");a=ap.parse_args();out=a.evidence.resolve()
    if out.is_relative_to(ROOT):raise SystemExit("Use off-Git evidence")
    frozen=subprocess.check_output(["git","show",BASE+":"+FILE],cwd=ROOT)
    assert (ROOT/FILE).read_bytes()==frozen
    declarations=scan(frozen.decode(),FILE);assert len(declarations)==7
    v.VERSION=json.loads((out/"serial/baseline-results.json").read_text())["version"];v.FINGERPRINTS.clear()
    v.checked_module(out/"serial",FILE)
    reports=[];pending=[]
    for row in declarations:
        name=row["source_name"]
        if name in PENDING:
            assert name not in v.WITNESSES and name not in v.IMPOSSIBLE
            item=PENDING[name];cert=v.certificate(out/"serial",item["module"],item["helper"])
            report=dict(row,status=item["status"],certificate=cert,question=item["question"],reason=item["reason"])
            pending.append(name)
        else:
            assert name in v.WITNESSES and name not in v.IMPOSSIBLE
            report=dict(row,status="joint-witness-checked",certificate=v.certificate(out/"serial",*v.WITNESSES[name]))
        reports.append(report)
    controls=[v.certificate(out/"serial","PayableWitnesses",n)for n in ["payable_system_positive_control","payable_enter_positive_control","payable_call_positive_control"]]
    assert len(pending)==1 and len(reports)==len({r["source_name"]for r in reports})==7
    payload={"frozen_base":BASE,"declarations":reports,"joint_witnesses":6,"pending_impossibilities":1,
      "H69_new_dispositions":0,"positive_model_API_controls":controls,
      "ordinary_joint_complete":False,"full_assignment_acceptance":False,
      "boundary":"Checked model System.run/World.enter/World.callFrame successes, not physical EVM totality. Static entry remains ordinary-interface blocked pending explicit scope disposition."}
    (out/"verified-payable.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("PAYABLE_SCOPE_ACCOUNTED:7originals,6joint,1pending-impossible,3positive-controls;full_acceptance=false")
    if a.require_joint_all:
        print("PAYABLE_JOINT_BLOCKED: "+pending[0]);raise SystemExit(1)

if __name__=="__main__":main()
