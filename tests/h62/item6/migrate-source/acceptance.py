#!/usr/bin/env python3
"""Independent import reconciliation and scanner negative controls; no Lean."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location("census",root/"scripts/h62/item6/migrate-source/census.py")
c=importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
assert c.imports("/- import False /- import False -/ -/\nimport A B -- import False\n") == ["A","B"]
assert c.imports('def s := "import False"\n-- import False\nimport A\n') == ["A"]
assert c.imports('public import A\nprivate meta import B\n') == ["A","B"]
assert c.mask("/- a\n/-b-/\nc-/").count("\n") == 2
census=json.loads(Path(sys.argv[1]).read_text())
tracked=subprocess.check_output(["git","-C",str(root),"ls-tree","-r","--name-only",c.BASE,"Solidity/Source"],text=True).splitlines()
assert sorted(f["path"] for f in census["files"]) == sorted(p for p in tracked if p.endswith(".lean"))
order=census["serial_build_order"]; pos={m:i for i,m in enumerate(order)}
assert {f["module"] for f in census["files"]} <= set(pos)
for m in order:
    text=subprocess.check_output(["git","-C",str(root),"show",census.get("revision",c.BASE)+":"+m.replace(".","/")+".lean"],text=True)
    # Independent raw header reconciliation: this pin uses one import per line.
    raw=[line.split()[1] for line in text.split("/-!",1)[0].splitlines() if line.startswith("import ")]
    assert raw == c.imports(text),m
    for dep in raw:
        if dep in pos: assert pos[dep] < pos[m],(m,dep)
assert not [m for m in census["nonlocal_imports"] if not m.startswith(("Lean", "Std", "Init"))],census["nonlocal_imports"]
assert len(order)==len(set(order))
print(f"PASS scanner negative controls; all {len(tracked)} original assigned Source files; all {len(order)} import headers reconciled at {census.get('revision',c.BASE)}; acyclic build order; no unresolved local imports")

spec=importlib.util.spec_from_file_location("comparison",root/"scripts/h62/item6/migrate-source/compare.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
import copy
r={"status":"pass","clean":True,"base":c.BASE,"census_revision":c.BASE,"modules":[{"module":"fixture","exit":0}],"wall_seconds":100,"sampled_peak_group_rss_bytes":100}
r.update({k:1 for k in m.PROFILE})
pin={"toolchain":"leanprover/lean4:v4.35.0","sha256":"fixture-pin"}
r["versions"]={"lean":"Lean (version 4.24.0, commit 797c613)","lake":"Lake version 5.0.0-src+797c613"}
n=copy.deepcopy(r);n["versions"]={"lean":"Lean (version 4.35.0, commit eb6cafb)","lake":"Lake version 5.0.0-src+eb6cafb"};n["archive_sha256"]="fixture-pin"
assert m.compare(r,n,["fixture"],c.BASE,pin)["status"]=="pass"
for value,want in [(110,"escalate"),(110.01,"stop"),(99,"pass")]:
    t=copy.deepcopy(n);t["wall_seconds"]=value
    assert m.compare(r,t,["fixture"],c.BASE,pin)["status"]==want
for change in ({"status":"fail"},{"modules":[]},{"lean_threads":2},{"wall_seconds":float("nan")},{"base":"wrong"},{"census_revision":"wrong-tree"},{"census_revision":None},{"versions":r["versions"]},{"archive_sha256":"wrong"}):
    t=copy.deepcopy(n);t.update(change)
    try: m.compare(r,t,["fixture"],c.BASE,pin)
    except ValueError: pass
    else: raise AssertionError("unsafe comparison accepted")
print("PASS comparison negative controls: incomplete/order/profile/NaN/base/version/pin rejection; 10% escalation and >10% STOP")

# A newer shared original base cannot make measurements of different trees comparable.
try:
    m.compare(r,n,["fixture"],c.BASE,pin,"new-operational-revision")
except ValueError:
    pass
else:
    raise AssertionError("stale same-base measurement accepted after re-baselining")
new_old=copy.deepcopy(r);new_new=copy.deepcopy(n)
new_old["census_revision"]=new_new["census_revision"]="new-operational-revision"
assert m.compare(new_old,new_new,["fixture"],c.BASE,pin,"new-operational-revision")["status"]=="pass"
print("PASS exact-revision controls: stale/missing/different census revisions rejected; matched new revision accepted")

modules={"Solidity.Source.Assigned":"Solidity/Source/Assigned.lean", "Solidity.Source.ProducerOnly":"Solidity/Source/ProducerOnly.lean"}
assert c.select_assigned(modules,["Solidity/Source/Assigned.lean"])==["Solidity.Source.Assigned"]
for paths in [[], ["Solidity/Source/Assigned.lean"]*2, ["Solidity/Source/Missing.lean"], ["Solidity/Other.lean"], ["Solidity/Source/../Other.lean"]]:
    try:
        c.select_assigned(modules,paths)
    except ValueError:
        pass
    else:
        raise AssertionError("invalid frozen scope accepted: "+repr(paths))
print("PASS explicit-scope controls: producer additions excluded; missing/duplicate/outside/traversal paths rejected")
