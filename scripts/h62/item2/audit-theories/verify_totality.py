#!/usr/bin/env python3
"""Verify current totality proof receipts; no new Lean jobs and no full-goal PASS.
All theorem names, source/import fingerprints, artifacts, logs and axiom sets
must agree. Semantic scope is explicit: target ABI/gas/fork remains unproved.
"""
import argparse,json,re
from pathlib import Path
import verify_census as verification
from census import ROOT,mask

FILES=("CoreTotality","CompilerAdmission","FailureGasForkBoundary")
PREFIX="H62.AuditTheories.CompilerAudit."

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--evidence",type=Path,required=True)
    a=ap.parse_args();out=a.evidence.resolve()
    if out.is_relative_to(ROOT):raise SystemExit("Use off-Git evidence")
    verification.VERSION=json.loads((out/"serial/baseline-results.json").read_text())["version"]
    verification.FINGERPRINTS.clear()
    reports=[]
    for module in FILES:
        source=f"tests/h62/item2/audit-theories/{module}.lean"
        meta,log=verification.checked_module(out/"serial",source)
        assert not re.search(r"\b(?:error(?:\([^)]*\))?|warning):",log),source
        assert "sorryAx" not in log,source
        names=re.findall(r"^theorem ([^\s:({]+)",mask((ROOT/source).read_text()),re.M)
        assert names,module
        theorems=[]
        for name in names:
            full=PREFIX+name
            match=re.search("'"+re.escape(full)+r"' (does not depend on any axioms|depends on axioms: \[([^]]*)\])",log)
            assert match,full
            axioms={v.strip() for v in (match[2] or "").split(",") if v.strip()}
            assert axioms<=verification.ALLOW,(full,axioms)
            theorems.append({"name":full,"axioms":sorted(axioms)})
        reports.append({"source":source,"command":meta["command"],"exit":meta["exit"],"seconds":meta["seconds"],"log":meta["log"],"source_transitive_sha256":meta["source_transitive_sha256"],"theorems":theorems})
    payload={"modules":reports,"proved_theorems":sum(len(r["theorems"]) for r in reports),
      "verified_scope":["Admission for every existing core-fragment certificate","Concrete bool source and actual public compiler success for both literals","Joint Input/simulation/growth/source/non-payment witnesses and a closed StandardExample case","Full original public Rep and stack success observations retained","Reject-all, always-revert and no-op compilers refuted","Core source panic/revert distinction collapses to target REVERT","Source stipend threshold400/399 and custom no-stipend/fork-pin boundaries"],
      "not_proved":["Target ABI failure bytes","Target gas-used/Fitted/Enforced","Execution agreement across physical forks","Success/admission for all non-core compiler branches","Remaining theory census witnesses and full final gates"],
      "full_assignment_acceptance":False}
    (out/"verified-totality.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("TOTALITY_RECEIPTS_PASS "+json.dumps({"modules":len(reports),"theorems":payload["proved_theorems"],"full_assignment_acceptance":False}))

if __name__=="__main__":main()
