#!/usr/bin/env python3
"""Six joint Payable packets and one explicitly accepted H69 separation boundary.
Ordinary coverage completes locally; joint-all intentionally cannot hold for the
static boundary. Neither its checked refutation nor this label proves refusal.
"""
import argparse,json,subprocess
from pathlib import Path
from census import ROOT,BASE,scan
import verify_census as v
from audit_dispositions import ACCEPTED,accepted_fields
FILE="Solidity/Theory/Mutability/Payable.lean"
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--evidence",required=True,type=Path)
    ap.add_argument("--require-joint-all",action="store_true");ap.add_argument("--require-ordinary-complete",action="store_true");a=ap.parse_args();out=a.evidence.resolve()
    if out.is_relative_to(ROOT):raise SystemExit("Use off-Git evidence")
    frozen=subprocess.check_output(["git","show",BASE+":"+FILE],cwd=ROOT);assert(ROOT/FILE).read_bytes()==frozen
    declarations=scan(frozen.decode(),FILE);assert len(declarations)==7
    v.VERSION=json.loads((out/"serial/baseline-results.json").read_text())["version"];v.FINGERPRINTS.clear();v.checked_module(out/"serial",FILE)
    reports=[];intentional=[]
    for row in declarations:
        name=row["source_name"]
        if name in ACCEPTED:
            assert name in v.IMPOSSIBLE and name not in v.WITNESSES
            item=ACCEPTED[name];report=dict(row,**accepted_fields(name),certificate=v.certificate(out/"serial",item["module"],item["helper"]));intentional.append(name)
        else:
            assert name in v.WITNESSES and name not in v.IMPOSSIBLE
            report=dict(row,status="joint-witness-checked",certificate=v.certificate(out/"serial",*v.WITNESSES[name]))
        reports.append(report)
    controls=[v.certificate(out/"serial","PayableWitnesses",n)for n in["payable_system_positive_control","payable_enter_positive_control","payable_call_positive_control"]]
    assert len(intentional)==1 and len(reports)==len({r["source_name"]for r in reports})==7
    payload={"frozen_base":BASE,"declarations":reports,"joint_witnesses":6,"pending_impossibilities":0,"accepted_H69":1,
      "positive_model_API_controls":controls,"ordinary_joint_complete":True,"static_operational_refusal_coverage":False,"full_assignment_acceptance":False,
      "boundary":"Static nonzero value is an explicit intentional H69 separation boundary. Its impossibility proof is the audit result; no operational refusal coverage. Other positive controls are model API successes, not physical EVM totality."}
    (out/"verified-payable.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("PAYABLE_ORDINARY_COMPLETE:7originals,6joint,1accepted-H69,0pending;static_operational_refusal_coverage=false;full_acceptance=false")
    if a.require_joint_all:
        print("PAYABLE_JOINT_ALL_INAPPLICABLE: intentional impossible inputs: "+intentional[0]);raise SystemExit(1)
if __name__=="__main__":main()
