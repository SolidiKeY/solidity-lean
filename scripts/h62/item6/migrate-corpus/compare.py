#!/usr/bin/env python3
"""Reject failed/incomparable timing runs; enforce the frozen slowdown rule."""
import json, math, pathlib, sys
from decimal import Decimal
old,new=[json.loads(pathlib.Path(x).read_text()) for x in sys.argv[1:3]]
keys=["threads","rss_stop_threshold_bytes","hard_vm_cap_bytes","reserve_bytes","swap_total_bytes","per_process_as_cap_bytes"]
result={"status":"BLOCKED","wall_delta_percent":None,"sampled_rss_delta_percent":None}
if any(x.get("exit")!=0 or x.get("resource_stop") for x in [old,new]):
    result["reason"]="A failed or stopped build is not a valid benchmark."
elif any(old.get(k)!=new.get(k) or k not in old or k not in new for k in keys):
    result["reason"]="Resource settings differ or are missing."
elif any(not isinstance(x.get(k),(int,float)) or not math.isfinite(x[k]) or x[k]<=0
         for x in [old,new] for k in ["wall_seconds","peak_aggregate_rss_bytes"]):
    result["reason"]="Nonpositive or missing measurements."
elif not old.get("benchmark") or old.get("benchmark")!=new.get("benchmark"):
    result["reason"]="Benchmark input/configuration/cache provenance missing or different."
elif old["benchmark"].get("schema")!="corpus-clean-v1" or old["benchmark"].get("clean") is not True:
    result["reason"]="Clean benchmark provenance required."
elif old["benchmark"].get("cache_policy")!="absent-output;artifact-cache-disabled;--no-cache" or old["benchmark"].get("targets")!=["SolidityCorpus"]:
    result["reason"]="Unsupported benchmark cache/workload policy."
elif any(x.get("command",[])[-2:]!=["build","SolidityCorpus"] for x in [old,new]):
    result["reason"]="Different or missing workload targets."
else:
    w=float(100*(Decimal(str(new["wall_seconds"]))/Decimal(str(old["wall_seconds"]))-1))
    r=100*(new["peak_aggregate_rss_bytes"]/old["peak_aggregate_rss_bytes"]-1)
    result.update(wall_delta_percent=w,sampled_rss_delta_percent=r)
    result["status"]="STOP" if Decimal(str(new["wall_seconds"]))>Decimal(str(old["wall_seconds"]))*Decimal("1.10") else ("ESCALATE" if w>0 or r>0 else "PASS")
    result["reason"]="Over 10% wall slowdown: stop." if result["status"]=="STOP" else ("Any measured regression requires escalation." if w>0 or r>0 else "No measured regression.")
print(json.dumps(result,indent=2))
raise SystemExit({"PASS":0,"BLOCKED":2,"STOP":3,"ESCALATE":4}[result["status"]])
