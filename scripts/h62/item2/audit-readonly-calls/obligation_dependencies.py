#!/usr/bin/env python3
"""Guard dropped frozen obligations and dependency observations promoted to proofs.

Join a pinned historical audit with a pinned header snapshot. Original witness and
owner fields remain historical; no-path never clears a timing hold. Current lexical
headers do not certify kernel meaning, global premises, feasibility or live ownership.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import subprocess

spec=importlib.util.spec_from_file_location("audit_fidelity",Path(__file__).with_name("fidelity_delta.py"))
fidelity=importlib.util.module_from_spec(spec);spec.loader.exec_module(fidelity)
census=fidelity.census
FROZEN_SHA="e07aa0fe5f1a94c292c6d9edc22eee478f45c560b1802fab5e7ac581da9a2ffb"
HELD="Solidity/Backend/WorldCalls/Premises.lean"
KIND="compiler-parsed-declared-header-dependency-inventory"
BOUNDARY="Historical witness/owner and declared-header observations only. Current kernel fidelity, live ownership, global premise inhabitation, joint feasibility and compiler adequacy are not inferred. All original obligations and the +80.254966536% Lean STOP remain."


def sha(raw):return hashlib.sha256(raw).hexdigest()


def pairs(items):
    result={}
    for key,value in items:
        if key in result:raise ValueError("duplicate JSON key")
        result[key]=value
    return result


def load_pinned(path,digest):
    raw=path.read_bytes()
    if sha(raw)!=digest:raise ValueError("input SHA256 mismatch")
    return json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda _: (_ for _ in ()).throw(ValueError("nonfinite JSON")))


def index(rows,key):
    result={row[key]:row for row in rows}
    if len(result)!=len(rows):raise ValueError("duplicate "+key)
    return result


def join(frozen,graph,current):
    modules=index(frozen["modules"],"file")
    if frozen["base"]!=census.BASE or frozen["theorem_count"]!=792 or len(frozen["declarations"])!=792 or len(modules)!=129:
        raise ValueError("wrong frozen census membership")
    if graph["original_base"]!=census.BASE or graph["original_obligations"]!=792 or graph["frozen_target_files"]!=129 or graph["frozen_map_sha256"]!=frozen["map_sha256"]:
        raise ValueError("dependency census mismatch")
    if graph.get("schema")!=1 or graph.get("kind")!=KIND or graph.get("held_module")!=HELD:
        raise ValueError("wrong dependency schema, kind or held module")
    # Old reports used path for both identity and dependency chain; never guess by order.
    if any("target" not in row for row in graph["targets"]):raise ValueError("missing explicit target identity")
    targets=index(graph["targets"],"target")
    if set(targets)!=set(modules):raise ValueError("dependency target membership mismatch")
    for name,target in targets.items():
        status=target["status"];path=target["path"]
        if status not in {"declared-path-to-held-module","no-declared-path-to-held-module","header-dependency-unknown"}:raise ValueError("invalid dependency status")
        if status=="declared-path-to-held-module":
            if not isinstance(path,list) or not path or path[0]!=name or path[-1]!=graph["held_module"]:raise ValueError("invalid declared path endpoints")
        elif path is not None:raise ValueError("unexpected dependency path")
        if status=="no-declared-path-to-held-module" and target["unknown"]:raise ValueError("no-path with unresolved dependencies")
        if status=="header-dependency-unknown" and not target["unknown"]:raise ValueError("unknown status without unresolved dependencies")
    original={(r["file"],r["source_name"]):r for r in frozen["declarations"]}
    if len(original)!=792 or any(k[0] not in modules for k in original):raise ValueError("invalid original declaration identities")
    observed=fidelity.compare(frozen["declarations"],current)
    rows=[]
    for delta in observed["original_obligations"]:
        key=(delta["file"],delta["source_name"]);target=targets[key[0]]
        rows.append({"frozen":original[key],"current_lexical_status":delta["source_status"],
                     "historical_header_dependency":target,"current_kernel_fidelity":"pending",
                     "live_ownership":"unverified","timing_hold":"retained"})
    counts=Counter((r["frozen"]["witness_status"],r["current_lexical_status"],r["historical_header_dependency"]["status"]) for r in rows)
    module_counts=Counter(r["file"] for r in frozen["declarations"])
    return {"schema":1,"base":census.BASE,"held_module":HELD,
            "modules":[{"file":name,"original_declarations":module_counts[name],"historical_header_dependency":targets[name]} for name in sorted(modules)],"boundary":BOUNDARY,"original_obligations":len(rows),"rows":rows,
            "witness_statuses":dict(Counter(r["frozen"]["witness_status"] for r in rows)),
            "lexical_statuses":observed["source_statuses"],"added_declarations":observed["added_declarations"],
            "cross_counts":[{"witness_status":k[0],"lexical_status":k[1],"header_status":k[2],"count":v} for k,v in sorted(counts.items())],
            "header_source_head":graph["source_head"],"header_snapshot_status":"historical; not recertified by this join"}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--frozen",type=Path,required=True);p.add_argument("--headers",type=Path,required=True)
    p.add_argument("--headers-sha256",required=True);p.add_argument("--output",type=Path,required=True)
    args=p.parse_args()
    frozen=load_pinned(args.frozen,FROZEN_SHA);graph=load_pinned(args.headers,args.headers_sha256)
    files=[row["file"] for row in frozen["modules"]];before={};current=[]
    head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=census.ROOT,text=True).strip()
    for name in files:
        path=PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or str(path)!=name:raise ValueError("unsafe source path")
        full=census.ROOT/name
        if full.resolve()!=full or not full.is_file():raise ValueError("noncanonical source")
        before[name]=sha(full.read_bytes());current.extend(census.declarations(name))
    result=join(frozen,graph,current)
    if any(sha((census.ROOT/name).read_bytes())!=digest for name,digest in before.items()):raise ValueError("source changed during lexical census")
    if subprocess.check_output(["git","rev-parse","HEAD"],cwd=census.ROOT,text=True).strip()!=head:raise ValueError("HEAD changed during census")
    result.update(current_source_head=head,current_source_sha256=before,frozen_sha256=FROZEN_SHA,header_inventory_sha256=args.headers_sha256)
    with args.output.open("x") as output:json.dump(result,output,sort_keys=True,indent=2);output.write("\n")
    print(json.dumps({k:result[k] for k in ("original_obligations","witness_statuses","lexical_statuses","cross_counts")}))


if __name__=="__main__":main()
