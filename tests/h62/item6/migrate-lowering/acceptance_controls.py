#!/usr/bin/env python3
"""Prevent a module regression or an incomplete/failed gate being misclassified."""
import hashlib, json, subprocess, sys, tempfile
from pathlib import Path
root=Path(__file__).resolve().parents[4]
script=root/"scripts/h62/item6/migrate-lowering/acceptance.py"
source="Solidity/Lowering/P9/DeclarationIdentity.lean"; module="Solidity.Lowering.P9.DeclarationIdentity"
with tempfile.TemporaryDirectory() as d:
    evidence=Path(d)/"evidence"; evidence.mkdir()
    (evidence/"census-base.json").write_text(json.dumps({"base":"fixture","modules":[{"module":module,"path":source,"sha256":hashlib.sha256((root/source).read_bytes()).hexdigest()}],"external_project_closure":[],"direct_external_edges":[]}))
    for label,wall,rss,duration in [("old",100,1000,"1s"),("new",90,900,"2s")]:
        (evidence/(label+"-clean-full.json")).write_text(json.dumps({"exit":0,"stop_reason":None,"wall_seconds":wall,"sampled_peak_group_rss_bytes":rss}))
        (evidence/(label+"-clean-full.log")).write_text(f"✔ [1/1] Built {module} ({duration})\n")
    def run():
        subprocess.run([sys.executable,str(script),"--artifacts",d],cwd=root,check=True,stdout=subprocess.DEVNULL)
        return json.loads((evidence/"acceptance.json").read_text())
    r=run(); assert r["all_assigned_modules_built_both"]
    assert r["modules"][0]["reported_wall_delta_percent"]==100
    assert r["modules"][0]["escalate_per_module"] and r["full_comparison"]=="resource-comparison-pass"
    (evidence/"new-clean-full.log").write_text("")
    assert not run()["all_assigned_modules_built_both"]
    (evidence/"new-clean-full.json").write_text(json.dumps({"exit":125,"stop_reason":"resource guard","wall_seconds":1,"sampled_peak_group_rss_bytes":1}))
    assert run()["full_comparison"]=="failed-gate"
    for key,value in [("wall_seconds",0),("sampled_peak_group_rss_bytes",0),("wall_seconds",float("nan")),("sampled_peak_group_rss_bytes",None)]:
        metric={"exit":0,"stop_reason":None,"wall_seconds":90,"sampled_peak_group_rss_bytes":900}; metric[key]=value
        (evidence/"new-clean-full.json").write_text(json.dumps(metric))
        assert run()["full_comparison"]=="missing-metric"
    (evidence/"new-clean-full.json").unlink()
    assert run()["full_comparison"]=="pending"
    (evidence/"old-clean-full.json").write_text(json.dumps({"exit":1,"stop_reason":None}))
    assert run()["full_comparison"]=="failed-gate"
print("PASS: module growth escalates without stopping; missing modules/results and failed gates cannot establish full acceptance")
