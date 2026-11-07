#!/usr/bin/env python3
"""Fail closed on incomplete or incomparable clean migration measurements."""
import argparse, json, pathlib, math
from decimal import Decimal
VERSIONS={"old":("4.24.0","797c613eb9b6d4ec95db23e3e00af9ac6657f24b","797c613"),"new":("4.35.0","eb6cafb7290e8bd5f2937522d8d804f58f02bafc","eb6cafb")}
RESOURCE_FIELDS=("cpu_affinity","cpu_max","memory_max","swap_table")

def compare(old,new):
    for label,r in (("old",old),("new",new)):
        version,commit,short=VERSIONS[label]
        if r["versions"]["lean"] != f"Lean (version {version}, x86_64-unknown-linux-gnu, commit {commit}, Release)" or r["versions"]["lake"] != f"Lake version 5.0.0-src+{short} (Lean version {version})":
            return {"status":"INCOMPARABLE","reason":label+" unexpected toolchain build"}
        if r.get("fixture") or r.get("imports"):
            return {"status":"INCOMPARABLE","reason":label+" is a fixture/cached-import run"}
        if not r["passed"] or len(r["records"])!=r["planned_modules"] or r["planned_modules"]!=64:
            return {"status":"INCOMPARABLE","reason":label+" full 64-module clean closure did not pass"}
        modules=[x.get("module") for x in r["records"]]
        if len(set(modules))!=64 or set(modules)!=set(r["closure_source_sha256"]) or any(x.get("source_sha256")!=r["closure_source_sha256"].get(x.get("module")) for x in r["records"]):
            return {"status":"INCOMPARABLE","reason":label+" incomplete/duplicate module or source-hash coverage"}
        if not r["provenance"].get("all_closure_sources_equal_base"):
            return {"status":"INCOMPARABLE","reason":label+" sources not verified against base"}
        if any(not isinstance(r[k],(int,float)) or isinstance(r[k],bool) or not math.isfinite(r[k]) or r[k]<=0 for k in ("wall_seconds","peak_aggregate_rss_bytes")):
            return {"status":"INCOMPARABLE","reason":label+" invalid measurement"}
        if any(type(x["exit"]) is not int or x["exit"] != 0 or x["resource_stop"] for x in r["records"]) or r["source_drift"]:
            return {"status":"INCOMPARABLE","reason":label+" errors, resource stop or source drift"}
    if old["settings"]!=new["settings"] or any(old["provenance"][k]!=new["provenance"][k] for k in RESOURCE_FIELDS) or old["closure_source_sha256"]!=new["closure_source_sha256"]:
        return {"status":"INCOMPARABLE","reason":"settings/resources/sources differ"}
    deltas={k:100*(new[k]/old[k]-1) for k in ("wall_seconds","peak_aggregate_rss_bytes")}
    metrics=("wall_seconds","peak_aggregate_rss_bytes")
    exceeds=any(Decimal(str(new[k]))>Decimal(str(old[k]))*Decimal("1.1") for k in metrics)
    regresses=any(Decimal(str(new[k]))>Decimal(str(old[k])) for k in metrics)
    status="STOP_GT_10_PERCENT" if exceeds else ("REGRESSION_ESCALATE" if regresses else "PASS")
    return {"status":status,"percent_change":deltas,"note":"directory olean-only comparison; repository final gate remains separate"}

if __name__=="__main__":
    ap=argparse.ArgumentParser();ap.add_argument("old",type=pathlib.Path);ap.add_argument("new",type=pathlib.Path);a=ap.parse_args()
    result=compare(json.loads(a.old.read_text()),json.loads(a.new.read_text()));print(json.dumps(result,sort_keys=True,indent=2))
    raise SystemExit(0 if result["status"]=="PASS" else 1)
