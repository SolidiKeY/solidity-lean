#!/usr/bin/env python3
"""Reproduce exact source census and account for each public theorem once.

Draft markers are candidate links only; this validator never awards proof credit.
"""
import argparse
import json
import re
from pathlib import Path
import census


def candidates(repo, rows):
    public = {r["name"] for r in rows if r["visibility"] == "public"}
    linked = {}
    for path in sorted((repo/"tests/h62/item2/audit-g25-scalar-lowering").glob("*.lean")):
        source = path.read_text()
        for match in re.finditer(r"-- AUDIT-WITNESS: ([\w.]+)\n(?:/[^\n]*\n)?theorem ([\w.]+)", source):
            original, witness = match.groups()
            if original not in public: raise ValueError("unfrozen witness marker: "+original)
            if original in linked: raise ValueError("duplicate witness marker: "+original)
            linked[original] = {"path":str(path.relative_to(repo)),
                                "declaration":"Solidity.Backend.Scalar.H62Audit."+witness,
                                "status":"draft-unverified"}
        if source.count("-- AUDIT-WITNESS:") != sum(1 for x in linked.values() if x["path"]==str(path.relative_to(repo))):
            raise ValueError("unparsed marker in "+str(path))
    return linked


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=Path.cwd())
    p.add_argument("--ownership", type=Path, required=True)
    p.add_argument("--census", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    repo = a.repo.resolve()
    actual = census.census(repo,json.loads(a.ownership.read_text()))
    saved = json.loads(a.census.read_text())
    if actual != saved: raise ValueError("census does not reproduce")
    links = candidates(repo,actual["theorems"])
    # Every public row appears once, including statements with no draft witness.
    ledger = [{"name":r["name"], "path":r["path"], "owner_key":r["owner_key"],
               "signature_sha256":r["signature_sha256"], "status":"uncovered",
               "candidate_witness":links.get(r["name"])}
              for r in actual["theorems"] if r["visibility"] == "public"]
    report = {"source_fidelity":"pass", "kernel_statement_fidelity":"pending",
              "public_rows":len(ledger), "draft_witnesses":len(links),
              "verified_witnesses":0, "uncovered":len(ledger),
              "without_draft":len(ledger)-len(links), "ledger":ledger}
    a.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k != "ledger"},sort_keys=True))
    print("ledger_sha256="+census.digest(a.output.read_bytes()))

if __name__ == "__main__": main()
