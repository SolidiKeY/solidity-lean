#!/usr/bin/env python3
"""Fail closed on incomplete runs; report measured regressions without waiving them."""
import argparse,json
from fractions import Fraction
from pathlib import Path
SETTINGS=("cpu","threads","lean_memory_mib","reserve_gib","swap","cache","timeout_seconds")
def compare(old,new):
 for run in (old,new):
  if run.get("status")!="pass" or not run.get("expected_modules") or run.get("completed_modules")!=run["expected_modules"]:
   raise ValueError("Incomplete/failed run cannot establish acceptance")
  if len(run["modules"])!=run["expected_modules"] or any(m["status"]!="pass" for m in run["modules"]):
   raise ValueError("Missing or failing module")
 if any(old[k]!=new[k] for k in SETTINGS): raise ValueError("Resource/cache settings differ")
 if [m["module"] for m in old["modules"]]!=[m["module"] for m in new["modules"]]: raise ValueError("Module coverage differs")
 wall=100*(new["wall_seconds"]/old["wall_seconds"]-1)
 rss=100*(max(m["max_rss_kib"] for m in new["modules"])/max(m["max_rss_kib"] for m in old["modules"])-1)
 wall_stop=Fraction(str(new["wall_seconds"]))>Fraction(str(old["wall_seconds"]))*Fraction(11,10)
 rss_stop=max(m["max_rss_kib"] for m in new["modules"])*10>max(m["max_rss_kib"] for m in old["modules"])*11
 return dict(wall_percent=wall,peak_rss_percent=rss,status="STOP" if wall_stop or rss_stop else "ESCALATE" if max(wall,rss)>0 else "pass")
if __name__=="__main__":
 ap=argparse.ArgumentParser();ap.add_argument("old",type=Path);ap.add_argument("new",type=Path);a=ap.parse_args()
 try: r=compare(json.loads(a.old.read_text()),json.loads(a.new.read_text()))
 except ValueError as e: print(json.dumps(dict(status="pending",reason=str(e))));raise SystemExit(2)
 print(json.dumps(r,indent=2));raise SystemExit(0 if r["status"]=="pass" else 1)
