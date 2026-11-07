#!/usr/bin/env python3
"""Reproduce exact source census and account for each public theorem once.

Draft markers alone never award proof credit. Proof mode requires bound
producer evidence, fresh receipt chains and exact kernel census checks.
"""
import argparse
import json
import re
from pathlib import Path
import census
import bounded_lean


def candidates(repo, rows):
    public = {r["name"] for r in rows if r["visibility"] == "public"}
    linked = {}
    for path in sorted((repo/"tests/h62/item2/audit-g25-scalar-lowering").rglob("*.lean")):
        source = path.read_text()
        markers = source.count("-- AUDIT-WITNESS:")
        if not markers: continue
        clean = census.mask(source)
        namespaces = re.findall(r"(?m)^namespace ([\w.]+)\s*$",clean)
        if len(namespaces) != 1: raise ValueError("unsupported witness namespace in "+str(path))
        namespace = namespaces[0]
        for match in re.finditer(r"-- AUDIT-WITNESS: ([\w.]+)\n(?:/[^\n]*\n)?theorem ([\w.]+)", source):
            original, witness = match.groups()
            if original not in public: raise ValueError("unfrozen witness marker: "+original)
            if original in linked: raise ValueError("duplicate witness marker: "+original)
            linked[original] = {"path":str(path.relative_to(repo)),
                                "declaration":namespace+"."+witness,
                                "status":"draft-unverified"}
        if source.count("-- AUDIT-WITNESS:") != sum(1 for x in linked.values() if x["path"]==str(path.relative_to(repo))):
            raise ValueError("unparsed marker in "+str(path))
    return linked


def validate_receipts(repo, cache, toolchain, required_evidence=None, targets=None):
    index=json.loads((cache/"cache-index.json").read_text())
    compiler=bounded_lean.distribution_hash(toolchain)
    fingerprints={}
    targets=targets or ["tests.h62.item2.audit-g25-scalar-lowering.AllWitnesses",
             "tests.h62.item2.audit-g25-scalar-lowering.KernelCensus"]
    ordered=bounded_lean.dependencies(repo,targets)
    for module in ordered:
        source=repo/(module.replace(".","/")+".lean")
        imported=[bounded_lean.module_name(name) for line in census.mask(source.read_text()).splitlines()
                  if line.startswith("import ") for name in line[7:].split()]
        data={"source":census.digest(source.read_bytes()),"compiler":compiler,
              "flags":["-j1","--tstack=131072"],
              "resource_policy":bounded_lean.RESOURCE_POLICY,
              "imports":{name:fingerprints.get(name,compiler) for name in imported}}
        expected=census.digest(json.dumps(data,sort_keys=True).encode())
        fingerprints[module]=expected
        entry=index[module]
        receipt=Path(entry["receipt"])
        if bounded_lean.digest_file(receipt)!=entry["receipt_sha256"]: raise ValueError("receipt hash mismatch: "+module)
        row=json.loads(receipt.read_text())
        output=cache/"lib/lean"/(module.replace(".","/")+".olean")
        digest=bounded_lean.digest_file(output)
        if not (entry["fingerprint"]==expected==row["fingerprint"] and
                entry["output_sha256"]==digest==row["output_sha256"] and
                row["source_sha256"]==data["source"] and row["exit"]==0 and
                row["resource_stop"] is False and row["cache_hit"] is False):
            raise ValueError("stale/nonpassing proof receipt: "+module)
        emitted=row.get("emitted_evidence",{})
        for path in (required_evidence or {}).get(module,[]):
            if str(path.resolve()) not in emitted: raise ValueError("unbound producer evidence: "+str(path))
        for path,sha in emitted.items():
            if bounded_lean.digest_file(Path(path))!=sha: raise ValueError("producer evidence hash mismatch: "+path)
    return len(ordered)


def verified_rows(path, kernel, links):
    data=json.loads(path.read_text())
    names={r["name"]:r for r in data}
    expected={r["name"]:r for r in kernel}
    if len(names)!=len(data) or set(names)!=set(expected): raise ValueError("verification statement census differs")
    for name,row in names.items():
        if row["witness"]!=links[name]["declaration"]: raise ValueError("witness declaration link differs: "+name)
        if row["kernel_type"]!=expected[name]["kernel_type"] or row["checked_binders"]!=expected[name]["binder_count"]:
            raise ValueError("frozen type/telescope census differs: "+name)
        if row["status"]!="verified-full-telescope-and-conclusion": raise ValueError("unverified row")
        if set(row["axioms"])-{"propext","Classical.choice","Quot.sound"}: raise ValueError("unexpected trust dependency")
    return names


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=Path.cwd())
    p.add_argument("--ownership", type=Path, required=True)
    p.add_argument("--census", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--verification",type=Path)
    p.add_argument("--kernel",type=Path)
    p.add_argument("--cache",type=Path)
    p.add_argument("--toolchain",type=Path)
    a = p.parse_args()
    repo = a.repo.resolve()
    actual = census.census(repo,json.loads(a.ownership.read_text()))
    saved = json.loads(a.census.read_text())
    if actual != saved: raise ValueError("census does not reproduce")
    links = candidates(repo,actual["theorems"])
    verified={}
    receipts=0
    if a.verification:
        if not all([a.kernel,a.cache,a.toolchain]): raise ValueError("proof credit requires kernel census/cache/toolchain")
        required={"tests.h62.item2.audit-g25-scalar-lowering.AllWitnesses":[a.verification],
                  "tests.h62.item2.audit-g25-scalar-lowering.KernelCensus":[a.kernel,a.kernel.parent/"premise-structures-v424.json"]}
        receipts=validate_receipts(repo,a.cache,a.toolchain,required)
        kernel_rows=json.loads(a.kernel.read_text())
        kernel_names=[row["name"] for row in kernel_rows]
        frozen_names={row["name"] for row in actual["theorems"] if row["visibility"]=="public"}
        if len(set(kernel_names))!=len(kernel_names) or set(kernel_names)!=frozen_names:
            raise ValueError("kernel census differs from frozen public source set")
        verified=verified_rows(a.verification,kernel_rows,links)
        for name in verified: links[name]["status"]="kernel-verified"
    # Every public row appears once; only fresh full-telescope kernel checks earn credit.
    ledger = [{"name":r["name"], "path":r["path"], "owner_key":r["owner_key"],
               "signature_sha256":r["signature_sha256"], "status":"verified" if r["name"] in verified else "uncovered",
               "candidate_witness":links.get(r["name"]),
               "verification":({"checked_binders":verified[r["name"]]["checked_binders"],
                                "axioms":verified[r["name"]]["axioms"],
                                "kernel_type_sha256":census.digest(verified[r["name"]]["kernel_type"].encode())}
                               if r["name"] in verified else None)}
              for r in actual["theorems"] if r["visibility"] == "public"]
    report = {"source_fidelity":"pass", "kernel_statement_fidelity":"pass" if verified else "pending",
              "public_rows":len(ledger), "linked_witnesses":len(links), "draft_witnesses":len(links)-len(verified),
              "verified_witnesses":len(verified), "uncovered":len(ledger)-len(verified),
              "validated_compilation_receipts":receipts,
              "without_candidate":len(ledger)-len(links), "ledger":ledger}
    a.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k != "ledger"},sort_keys=True))
    print("ledger_sha256="+census.digest(a.output.read_bytes()))

if __name__ == "__main__": main()
