#!/usr/bin/env python3
"""Validate every additive proof module and theorem receipt; no Lean jobs.
This verifies kernel-check provenance and the axiom allowlist, not semantic
coverage or full-assignment acceptance. All generators remain outside core.
"""
import argparse,json,re
from pathlib import Path
from census import ROOT,scan,mask
import verify_census as verification

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--evidence",required=True,type=Path)
    a=ap.parse_args();out=a.evidence.resolve()
    if out.is_relative_to(ROOT):raise SystemExit("Use off-Git evidence")
    verification.VERSION=json.loads((out/"serial/baseline-results.json").read_text())["version"]
    verification.FINGERPRINTS.clear()
    reports=[];seen=set();definitions=0;abbreviations=0
    for path in sorted((ROOT/"tests/h62/item2/audit-theories").rglob("*.lean")):
        source=path.relative_to(ROOT).as_posix();text=path.read_text()
        if path.name=="ElaboratedCensus.lean":
            assert not scan(text,source),"Metaprogram unexpectedly declares proofs"
            continue
        declarations=scan(text,source)
        assert declarations,source
        meta,log=verification.checked_module(out/"serial",source)
        assert meta["command"][-1]==source,source
        assert not re.search(r"\b(?:error(?:\([^)]*\))?|warning):",log),source
        assert "sorryAx" not in log,source
        theorems=[]
        for declaration in declarations:
            name=declaration["source_name"]
            assert name.startswith("H62.AuditTheories.") and name not in seen,name
            seen.add(name)
            match=re.search("'"+re.escape(name)+r"' (does not depend on any axioms|depends on axioms: \[([^]]*)\])",log)
            assert match,name
            axioms={v.strip() for v in (match[2] or "").split(",") if v.strip()}
            assert axioms<=verification.ALLOW,(name,axioms)
            theorems.append({"name":name,"axioms":sorted(axioms)})
        plain=mask(text)
        definitions+=len(re.findall(r"^def ",plain,re.M))
        abbreviations+=len(re.findall(r"^private abbrev ",plain,re.M))
        reports.append({"source":source,"command":meta["command"],"exit":meta["exit"],"seconds":meta["seconds"],"log":meta["log"],"source_transitive_sha256":meta["source_transitive_sha256"],"theorems":theorems})
    payload={"modules":reports,"proved_theorems":len(seen),"fixture_predicate_definitions":definitions,"private_type_abbreviations":abbreviations,"full_assignment_acceptance":False,"boundary":"Receipt/axiom verification only. Original theorem input fidelity and semantic scope require separate census, totality evidence and read-only reviews."}
    (out/"verified-helpers.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("HELPER_RECEIPTS_PASS "+json.dumps({k:v for k,v in payload.items() if k!="modules"}))

if __name__=="__main__":main()
