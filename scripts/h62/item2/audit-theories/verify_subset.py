#!/usr/bin/env python3
"""Validate explicit joint-input coverage ONLY for selected unchanged frozen files.
This does not bypass whole-census guards, disposition generated declarations,
or establish whole-assignment acceptance. Receipt checks are external validation;
statement/input fidelity still requires independent read-only source review.
"""
import argparse,json,re,subprocess
from pathlib import Path
from census import ROOT,BASE,MAP,scan
import verify_census as verification

def refuse(reason):
    raise SystemExit("SUBSET_REFUSED: "+reason)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--evidence",required=True,type=Path)
    ap.add_argument("--module",required=True,action="append")
    ap.add_argument("--report",type=Path,help="Separate off-Git report destination; preserves proof evidence inputs")
    a=ap.parse_args();out=a.evidence.resolve()
    if out.is_relative_to(ROOT):refuse("use off-Git evidence")
    report=a.report.resolve() if a.report else out/"verified-subset.json"
    if report.is_relative_to(ROOT):refuse("use an off-Git report destination")
    if len(a.module)!=len(set(a.module)):refuse("duplicate module")
    frozen_map=subprocess.check_output(["git","show",BASE+":"+MAP],cwd=ROOT,text=True)
    allowed={"Solidity/"+f for f in re.findall(r"^\| `(Theory/[^`]+\.lean)`",frozen_map,re.M)}
    declarations=[]
    for module in a.module:
        if module not in allowed:refuse("outside original frozen module map: "+module)
        frozen=subprocess.check_output(["git","show",BASE+":"+module],cwd=ROOT)
        current=(ROOT/module).read_bytes()
        if current!=frozen:refuse("frozen source changed: "+module)
        rows=scan(current.decode(),module)
        if not rows:refuse("no explicit declarations: "+module)
        missing=[r["source_name"] for r in rows if r["source_name"] not in verification.WITNESSES]
        if missing:refuse(f"{len(missing)} explicit joint witnesses missing: "+module)
        declarations.extend(rows)
    verification.VERSION=json.loads((out/"serial/baseline-results.json").read_text())["version"]
    verification.FINGERPRINTS.clear()
    reports=[];seen=set()
    for module in a.module:
        meta,log=verification.checked_module(out/"serial",module)
        assert meta["command"][-1]==module,module
    for row in declarations:
        name=row["source_name"]
        assert name not in seen,name
        seen.add(name)
        certificate=verification.certificate(out/"serial",*verification.WITNESSES[name])
        reports.append(dict(row,status="joint-witness-checked",certificate=certificate))
    payload={"frozen_assignment_base":BASE,
      "current_head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),
      "selected_modules":a.module,"joint_explicit_statements":len(reports),"declarations":reports,
      "generated_candidates_dispositioned":0,"full_assignment_acceptance":False,
      "boundary":"Selected unchanged source files and checked input certificates only; no equivalence claim for changed definitions elsewhere. Full census and current/frozen version fidelity remain separate."}
    report.parent.mkdir(parents=True,exist_ok=True)
    report.write_text(json.dumps(payload,indent=2)+"\n")
    print("SUBSET_EXPLICIT_INPUT_PASS "+json.dumps({"modules":len(a.module),"joint_explicit_statements":len(reports),"full_assignment_acceptance":False}))

if __name__=="__main__":main()
