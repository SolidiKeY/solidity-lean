#!/usr/bin/env python3
"""Fail closed when clean matched migration timings cannot be compared.
This is a timing gate, not a Lean proof or acceptance override.
"""
import argparse, json, math, pathlib

def compare(old,new):
    errors=[]
    for label,r in [("old",old),("new",new)]:
        if r.get("comparison_scope")!="directory" or r.get("build_kind")!="lake-leanArts":
            errors.append(label+": not a full directory Lake comparison; module changes are record-only")
    expected=[("4.24.0","797c613eb9b6d4ec95db23e3e00af9ac6657f24b","797c613","b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec"),
      ("4.35.0","eb6cafb7290e8bd5f2937522d8d804f58f02bafc","eb6cafb","7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d")]
    for label,r,(version,commit,short,archive) in zip(["old","new"],[old,new],expected):
        versions=r.get("versions",{})
        lean=f"Lean (version {version}, x86_64-unknown-linux-gnu, commit {commit}, Release)"
        lake=f"Lake version 5.0.0-src+{short} (Lean version {version})"
        if versions!={"lean":lean,"lake":lake} or r.get("toolchain_archive_sha256")!=archive:
            errors.append(label+": unexpected compiler or official archive identity")
        wall=r.get("wall_s")
        if not isinstance(wall,(int,float)) or isinstance(wall,bool) or not math.isfinite(wall) or wall<=0:
            errors.append(label+": invalid wall time")
    for key in ["runner_sha256","census_runner_sha256","lake_profile_sha256"]:
        a=old.get("source_before",{}).get(key); b=new.get("source_before",{}).get(key)
        if not a or a!=b: errors.append("absent/different "+key)
    for label,r in [("old",old),("new",new)]:
        if r.get("status")!="pass" or r.get("failure"): errors.append(label+": unsuccessful build")
        if r.get("clean") is not True or r.get("dependency_libs"): errors.append(label+": focused/cache-assisted run")
        if not r.get("source_before") or r.get("source_before")!=r.get("source_after"): errors.append(label+": absent/changed source provenance")
    if old.get("targets")!=new.get("targets"): errors.append("target sets differ")
    if [r["module"] for r in old.get("rows",[])] != [r["module"] for r in new.get("rows",[])]: errors.append("built module sets differ")
    if old.get("resources")!=new.get("resources"): errors.append("resource settings differ")
    for r in [old,new]:
        if not r.get("rows") or any(x.get("exit")!=0 or x.get("stop") for x in r.get("rows",[])): errors.append("incomplete or stopped module set")
    if errors: return {"status":"blocked","delta_percent":None,"reasons":errors}
    delta=100*(new["wall_s"]/old["wall_s"]-1)
    return {"status":"STOP" if delta>10 else "escalate" if delta>0 else "pass", "delta_percent":delta,
      "note":"Module time/memory increases are recorded without stopping a lane (coordinator clarification). Only matched full directory build slowdown uses this threshold. Source hashes are recorded in both reports. Owner-reviewed API adaptations may differ; exact interface preservation is a separate required gate."}
if __name__=="__main__":
    p=argparse.ArgumentParser(); p.add_argument("old",type=pathlib.Path); p.add_argument("new",type=pathlib.Path); a=p.parse_args()
    result=compare(json.loads(a.old.read_text()),json.loads(a.new.read_text()))
    print(json.dumps(result,indent=2)); raise SystemExit(result["status"]!="pass")
