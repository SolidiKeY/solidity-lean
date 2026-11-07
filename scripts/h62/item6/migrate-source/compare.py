#!/usr/bin/env python3
"""Fail closed on incomplete/different runs; metrics do not prove API equivalence."""
from decimal import Decimal
import json
from pathlib import Path
import sys

PROFILE=("lean_threads","lean_heap_mib","sampled_rss_stop_bytes","reserve_bytes","stack_kib","parent_rlimit_as","cgroup_memory_max","cpu_quota","cpuset")
def compare(old,new,expected,base,pin,revision=None):
    for r in (old,new):
        if r.get("status")!="pass" or r.get("clean") is not True: raise ValueError("complete passing clean builds required")
        if [x["module"] for x in r["modules"]]!=expected or any(x.get("exit")!=0 for x in r["modules"]): raise ValueError("complete identical module order required")
    if old["base"]!=base or new["base"]!=base: raise ValueError("reports differ from census pinned base")
    revision = base if revision is None else revision
    if any(r.get("census_revision") != revision for r in (old,new)):
        raise ValueError("reports must match the exact census revision; original base alone is insufficient")
    for r,version,commit in ((old,"4.24.0","797c613"),(new,"4.35.0","eb6cafb")):
        v=r.get("versions",{})
        if not v.get("lean","").startswith("Lean (version "+version+",") or commit not in v["lean"] or not v.get("lake","").startswith("Lake version 5.0.0-src+"+commit):
            raise ValueError("incorrect old/new toolchain identity")
    if pin.get("toolchain")!="leanprover/lean4:v4.35.0" or new.get("archive_sha256")!=pin.get("sha256") or not pin.get("sha256"):
        raise ValueError("target archive differs from official coordinator pin")
    if any(k not in old or k not in new or old[k]!=new[k] for k in PROFILE): raise ValueError("different or missing resource profile")
    deltas={}
    for key in ("wall_seconds","sampled_peak_group_rss_bytes"):
        a,b=Decimal(str(old[key])),Decimal(str(new[key]))
        if not a.is_finite() or not b.is_finite() or a<=0 or b<=0: raise ValueError("invalid measurement")
        deltas[key]=100*(b/a-1)
    status="stop" if any(v>10 for v in deltas.values()) else "escalate" if any(v>0 for v in deltas.values()) else "pass"
    return {"status":status,"delta_percent":{k:str(v) for k,v in deltas.items()},"boundary":"complete build metrics only; API/proof/review gates separate"}
if __name__=="__main__":
    try:
        a,b,c,pin=map(lambda p:json.loads(Path(p).read_text()),sys.argv[1:])
        result=compare(a,b,c["serial_build_order"],c["base"],pin,c.get("revision",c["base"]))
    except (ValueError,KeyError) as e:
        print(json.dumps({"status":"blocked","reason":str(e)}));sys.exit(4)
    print(json.dumps(result));sys.exit({"pass":0,"escalate":2,"stop":3}[result["status"]])
