#!/usr/bin/env python3
"""Fail closed on incomplete/mismatched runs. Every regression escalates."""
import argparse, hashlib, json, math, re
from decimal import Decimal
from pathlib import Path

def compare(old, new):
    for name,s in (("old",old),("new",new)):
        if s.get("status")!="pass" or not s.get("full_assigned_build"):
            return {"status":"pending","blocker":"INCOMPLETE_FULL_BUILD","run":name}
        if [r["module"] for r in s["results"]]!=s["requested_modules"] or any(r["exit"] or r["stop"] for r in s["results"]):
            return {"status":"fail","blocker":"INCONSISTENT_BUILD_RECORDS","run":name}
    for name,s,version,commit in (("old",old,"4.24.0","797c613eb9b6d4ec95db23e3e00af9ac6657f24b"),("new",new,"4.35.0","eb6cafb7290e8bd5f2937522d8d804f58f02bafc")):
        versions=s.get("versions",{})
        if f"version {version}," not in versions.get("lean","") or commit not in versions.get("lean","") or f"Lean version {version}" not in versions.get("lake",""):
            return {"status":"blocked","blocker":"UNEXPECTED_TOOLCHAIN","run":name}
        values=[s["wall_s"]]+[r["sampled_aggregate_peak_rss_bytes"] for r in s["results"]]
        if any(not isinstance(v,(int,float)) or not math.isfinite(v) or v<=0 for v in values):
            return {"status":"fail","blocker":"INVALID_METRIC","run":name}
        path=Path(s["results"][0]["command"][2])
        if hashlib.sha256(path.read_bytes()).hexdigest()!=s.get("config_sha256"):
            return {"status":"fail","blocker":"CONFIG_DIGEST_MISMATCH","run":name}
    for field in ("requested_modules","source_hashes","settings","resources","parent_resources","runtime_image","cpu_affinity"):
        if old[field]!=new[field]: return {"status":"blocked","blocker":"UNMATCHED_MEASUREMENT","field":field}
    # Private buildDir is intentionally different; all other config bytes must match.
    def config(s):
        path=Path(s["results"][0]["command"][2])
        return re.sub(r'(?m)^buildDir = .*$', 'buildDir = "PRIVATE"',path.read_text())
    if config(old)!=config(new): return {"status":"blocked","blocker":"UNMATCHED_CONFIG"}
    wall=(new["wall_s"]/old["wall_s"]-1)*100
    oldrss=max(r["sampled_aggregate_peak_rss_bytes"] for r in old["results"])
    newrss=max(r["sampled_aggregate_peak_rss_bytes"] for r in new["results"])
    rss=(newrss/oldrss-1)*100
    stop=Decimal(str(new["wall_s"])) > Decimal(str(old["wall_s"]))*Decimal("1.1") or newrss*10>oldrss*11
    regression=new["wall_s"]>old["wall_s"] or newrss>oldrss
    return {"status":"stop" if stop else "escalate" if regression else "pass","wall_delta_percent":wall,"sampled_peak_rss_delta_percent":rss,"old_wall_s":old["wall_s"],"new_wall_s":new["wall_s"],"old_sampled_peak_rss_bytes":oldrss,"new_sampled_peak_rss_bytes":newrss}
if __name__=="__main__":
    ap=argparse.ArgumentParser(); ap.add_argument("old",type=Path); ap.add_argument("new",type=Path); a=ap.parse_args()
    result=compare(json.loads(a.old.read_text()),json.loads(a.new.read_text())); print(json.dumps(result,indent=2)); raise SystemExit(0 if result["status"]=="pass" else 1)
