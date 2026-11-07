#!/usr/bin/env python3
"""Refuse partial comparisons; enforce the frozen wall/RSS regression gates."""
import argparse, json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument("old",type=Path);ap.add_argument("new",type=Path);a=ap.parse_args()
old=json.loads(a.old.read_text());new=json.loads(a.new.read_text())
settings=["base","cpu","lean_threads","lean_args","artifact_cache","address_space_limit_gib","reserve_gib"]
mismatches=[k for k in settings if old.get(k)!=new.get(k)]
# Legacy old-clean-2 mislabeled whole-cgroup usage; its actual bound was 12 GiB.
def bound(x):return x.get("cgroup_usage_limit_gib",x.get("aggregate_rss_limit_gib"))
if bound(old)!=bound(new):mismatches.append("cgroup_usage_limit_gib")
def complete(x):return x.get("status")=="pass" and all(m.get("exit")==0 for m in x["modules"])
if mismatches or not complete(old) or not complete(new) or {m['module'] for m in old['modules']}!={m['module'] for m in new['modules']}:
 print(json.dumps({"status":"blocked","type":"incomplete-or-incomparable-build","settings_mismatches":mismatches,"old_status":old['status'],"new_status":new['status'],"wall_delta_percent":None,"rss_delta_percent":None},indent=2));raise SystemExit(1)
def rss(x):return max(m["max_rss_kib"] for m in x["modules"])
wall=(new['wall_s']/old['wall_s']-1)*100;memory=(rss(new)/rss(old)-1)*100
status="STOP" if max(wall,memory)>10 else "escalate" if max(wall,memory)>0 else "pass"
print(json.dumps({"status":status,"wall_delta_percent":wall,"rss_delta_percent":memory,"rss_metric":"maximum wait4 child ru_maxrss; not cgroup memory.current"},indent=2))
raise SystemExit(0 if status=="pass" else 2)
