#!/usr/bin/env python3
"""Generate an old-only import audit and canonical per-declaration/type hashes."""
import argparse, collections, fcntl, hashlib, json, re
from pathlib import Path

def canonical(value):return json.dumps(value,ensure_ascii=False,sort_keys=True,separators=(",",":")).encode()
def require_complete_count(expected,observed):
    if expected!=observed:raise RuntimeError(f"Truncated/extra declaration stream: expected {expected}, observed {observed}")
def main():
    a=argparse.ArgumentParser();a.add_argument("mode",choices=["prepare","hash"]);a.add_argument("root");a.add_argument("census");a.add_argument("output");args=a.parse_args()
    root=Path(args.root).resolve();out=Path(args.output).resolve();out.mkdir(parents=True,exist_ok=True)
    census=json.loads(Path(args.census).read_text());modules=[r["module"] for r in census["modules"]]
    if args.mode=="prepare":
        lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        template=(root/"tests/h62/item6/migrate-calculus/InterfaceEncoder.lean").read_text()
        imports="import Lean\n"+"".join("import "+m+"\n" for m in modules)
        expected="def expectedModules : Array String := #["+",".join(json.dumps(m) for m in modules)+"]"
        marker="def expectedModules : Array String := #[] -- H62_EXPECTED_MODULES"
        if template.count(marker)!=1:raise RuntimeError("Expected-module template marker mismatch")
        source=imports+template.removeprefix("import Lean\n").replace(marker,expected)
        path=root/"tests/h62/item6/migrate-calculus/GeneratedFrozenTypes.lean"
        if path.exists() and path.read_text()!=source:raise RuntimeError("Preserve unexpected generated audit")
        path.write_text(source);(out/path.name).write_text(source);print(path)
        return
    result_path=out/"result.json";result=json.loads(result_path.read_text())
    if result["status"]!="pass" or not result.get("audit_reuses_owned_baseline"):
        raise RuntimeError("Type hashing requires a successful owned-baseline audit")
    if result["source_provenance"]!=census["closure_sources"]:raise RuntimeError("Audit/census source mismatch")
    jobs=[job for job in result["results"] if job["module"].endswith("GeneratedFrozenTypes.lean")]
    if len(jobs)!=1 or jobs[0]["exit"]!=0:raise RuntimeError("Missing completed type-audit job")
    log_path=Path(jobs[0]["log"]);log=log_path.read_text()
    summary=re.findall(r"Frozen baseline types: (\d+) modules, (\d+) declarations",log)
    if len(summary)!=1 or int(summary[0][0])!=len(modules):raise RuntimeError("Missing/mismatched audit completion summary")
    expected_count=int(summary[0][1])
    rows={m:[] for m in modules};seen=set();counts=collections.Counter();raw_hash=hashlib.sha256()
    source=out/"frozen-types.ndjson"
    with source.open("rb") as stream:
        for line in stream:
            raw_hash.update(line)
            row=json.loads(line);module=row["module"];key=canonical(row["name_tree"])
            if module not in rows or key in seen:raise RuntimeError("Unexpected/duplicate declaration")
            if row["unsafe"]:counts["baseline_unsafe"]+=1
            digest=hashlib.sha256(canonical(row)).hexdigest()
            seen.add(key);counts[row["kind"]]+=1
            rows[module].append(dict(module=module,name=row["name"],name_key=key.decode(),kind=row["kind"],sha256=digest))
    require_complete_count(expected_count,len(seen))
    if not seen:raise RuntimeError("Empty frozen declaration inventory")
    inventory=[]
    with (out/"declaration-type-sha256.ndjson").open("w") as stream:
        for module in modules:
            ordered=sorted(rows[module],key=lambda r:r["name_key"]);digests=[]
            for row in ordered:
                digest=row["sha256"];digests.append(digest)
                stream.write(json.dumps({k:v for k,v in row.items() if k!="name_key"},ensure_ascii=False)+"\n")
            inventory.append(dict(module=module,declarations=len(ordered),sha256=hashlib.sha256(canonical(ordered)).hexdigest()))
    manifest=dict(format="h62-expr-v1",audit_result_sha256=hashlib.sha256(result_path.read_bytes()).hexdigest(),audit_log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest(),raw_stream_sha256=raw_hash.hexdigest(),audited_declaration_count=expected_count,baseline_axiom_declarations=counts.get("axiom",0),private_declarations=sum(1 for group in rows.values() for row in group if row["name"].startswith("_private.")),base=census["base"],module_count=len(modules),declarations=len(seen),baseline_unsafe_declarations=counts.pop("baseline_unsafe",0),kinds=dict(counts),metadata_stripped=True,includes_private_generated=True,proof_bodies_exported=False,semantic_equivalence_proved=False,modules=inventory)
    (out/"frozen-interface-manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
    print(json.dumps({k:v for k,v in manifest.items() if k!="modules"}))
if __name__=="__main__":main()
