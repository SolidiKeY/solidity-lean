#!/usr/bin/env python3
"""Off-Git acceptance/progress report; per-module growth never stops a lane (QPERF1)."""
import argparse, hashlib, json, math, re
from pathlib import Path
p=argparse.ArgumentParser(); p.add_argument("--artifacts",type=Path,default=Path("/workspace/migrate-lowering-artifacts")); a=p.parse_args()
e=a.artifacts/"evidence"; census=json.loads((e/"census-base.json").read_text()); root=Path.cwd()
expected={r["module"]:r for r in census["modules"]}
def modules(log):
    found={}
    if not log.exists(): return found
    for line in log.read_text().splitlines():
        m=re.match(r"^[✔⚠ℹ]\ufe0f? \[\d+/\d+\] Built (\S+) \(([^)]+)\)",line)
        if not m or m[1] not in expected: continue
        duration=m[2]; parts=re.findall(r"([0-9.]+)(ms|s|m|h)",duration)
        seconds=sum(float(n)*{"ms":0.001,"s":1,"m":60,"h":3600}[unit] for n,unit in parts) if parts else None
        found[m[1]]={"duration_reported":duration,"seconds":seconds}
    return found
old=modules(e/"old-clean-full.log"); new=modules(e/"new-clean-full.log")
rows=[]
for name,r in sorted(expected.items()):
    before=old.get(name); after=new.get(name); delta=None
    if before and after and before["seconds"] and after["seconds"] is not None:
        delta=100*(after["seconds"]/before["seconds"]-1)
    rows.append({"module":name,"old":before,"new":after,"reported_wall_delta_percent":delta,"escalate_per_module":delta is not None and delta>0})
metrics={}
for label in ("old","new"):
    path=e/(label+"-clean-full.json")
    metrics[label]=json.loads(path.read_text()) if path.exists() else None
comparison="pending"; wall=None; rss=None
if any(m is not None and (m.get("exit")!=0 or m.get("stop_reason")) for m in metrics.values()):
    comparison="failed-gate"
elif all(metrics.values()):
    x,y=metrics["old"],metrics["new"]
    settings=("cgroup_cap_bytes","reserve_bytes","LEAN_NUM_THREADS","sample_interval_seconds","memory_policy","guard_sha256","config_sha256","cpu_max","cpuset_cpus_effective","affinity_cpus")
    if any(k not in m for m in (x,y) for k in settings): comparison="missing-resource-provenance"
    elif any(x[k]!=y[k] for k in settings): comparison="resource-settings-mismatch"
    elif not all(isinstance(m.get(k),str) and len(m[k])==64 for m in (x,y) for k in ("guard_sha256","config_sha256")): comparison="missing-resource-provenance"
    elif not all(isinstance(m.get(k),(int,float)) and math.isfinite(m[k]) and m[k]>0 for m in (x,y) for k in ("wall_seconds","sampled_peak_group_rss_bytes")): comparison="missing-metric"
    else:
        wall=100*(y["wall_seconds"]/x["wall_seconds"]-1)
        rss=100*(y["sampled_peak_group_rss_bytes"]/x["sampled_peak_group_rss_bytes"]-1)
        comparison="stop-over-10-percent" if max(wall,rss)>10 else "escalation" if max(wall,rss)>0 else "resource-comparison-pass"
changed=[r["path"] for r in expected.values() if hashlib.sha256((root/r["path"]).read_bytes()).hexdigest()!=r["sha256"]]
external=[]
for name in census["external_project_closure"]:
    path=Path(*name.split(".")).with_suffix(".lean")
    external.append({"module":name,"path":str(path),"source_sha256":hashlib.sha256((root/path).read_bytes()).hexdigest(),"write_authority":"external owner only"})
report={"base":census["base"],"expected_assigned_modules":len(expected),"old_built_assigned_modules":len(old),"new_built_assigned_modules":len(new),"all_assigned_modules_built_both":len(old)==len(new)==len(expected),"source_changed_since_census":changed,"full_comparison":comparison,"wall_delta_percent":wall,"sampled_rss_delta_percent":rss,"per_module_policy":"QPERF1: record and escalate module growth; only matched clean full comparison governs stop","modules":rows,"direct_external_edges":census["direct_external_edges"],"external_project_closure":external,"boundaries":"Build logs and source hashes do not replace elaborated type/axiom compatibility or independent milestone review. Missing module rows are pending, never acceptance."}
output=e/"acceptance.json"; output.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({k:report[k] for k in ("expected_assigned_modules","old_built_assigned_modules","new_built_assigned_modules","all_assigned_modules_built_both","full_comparison")},sort_keys=True))
