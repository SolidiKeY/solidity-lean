#!/usr/bin/env python3
"""Finite negative controls for tooling acceptance, without running Lean."""
import copy, hashlib, json, pathlib, subprocess, tempfile
import sys
sys.dont_write_bytecode = True
from census import ROOT, TARGETS, census, closure, imports, uncomment
from compare import compare
x=census()
assert len(x["files"])==3 and len(x["closure_order"])==64
assert all(f["unchanged"] and not any(f["trust_tokens"].values()) for f in x["files"].values())
assert len(x["files"]["Solidity.SortCheck.Faithfulness"]["generated_theorems"])==46
assert len(x["files"]["Solidity.SortCheck.Parser"]["where_declarations"])==1
try: closure(["Solidity.SortCheck.DoesNotExist"])
except ValueError: pass
else: raise AssertionError("missing module was accepted")
assert uncomment('/- a /- nested -/ b -/ import X\n') .strip()=="import X"
assert uncomment('"/- literal -/" -- line\n').strip()=='"/- literal -/"'
r={"status":"pass","failure":None,"clean":True,"source_before":{"head":"synthetic","source_sha256":{"A":"h"},"runner_sha256":"synthetic-runner","census_runner_sha256":"synthetic-census","lake_profile_sha256":"synthetic-lake-profile"},
 "source_after":{"head":"synthetic","source_sha256":{"A":"h"},"runner_sha256":"synthetic-runner","census_runner_sha256":"synthetic-census","lake_profile_sha256":"synthetic-lake-profile"},"targets":["A"],"resources":{"threads":1},
 "comparison_scope":"directory","build_kind":"lake-leanArts","rows":[{"module":"A","exit":0,"stop":None}],"wall_s":100}
r["versions"]={"lean":"Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)","lake":"Lake version 5.0.0-src+797c613 (Lean version 4.24.0)"}
r["toolchain_archive_sha256"]="b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec"
n=copy.deepcopy(r)
n["versions"]={"lean":"Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)","lake":"Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)"}
n["toolchain_archive_sha256"]="7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d"
assert compare(r,n)["status"]=="pass"
assert compare(r,r)["status"]=="blocked" # same compiler cannot prove migration timing
for field,value in [("status","fail"),("clean",False),("source_after",{}),("rows",[]),("wall_s",float("nan")),("wall_s",0),("toolchain_archive_sha256","wrong"),("comparison_scope","module"),("build_kind","per-file-elaboration")]:
    bad=copy.deepcopy(n); bad[field]=value; assert compare(r,bad)["status"]=="blocked",field
bad=copy.deepcopy(n)
for side in ["source_before","source_after"]: bad[side]["runner_sha256"]="different-runner"
assert compare(r,bad)["status"]=="blocked"
for wall,status in [(101,"escalate"),(111,"STOP")]:
    changed=copy.deepcopy(n); changed["wall_s"]=wall; assert compare(r,changed)["status"]==status
with tempfile.TemporaryDirectory() as td:
    overlay=pathlib.Path(td)/"overlay"; (overlay/"Solidity").mkdir(parents=True)
    (overlay/"Solidity/First.lean").write_text("import Solidity.Second\n")
    (overlay/"Solidity/Second.lean").write_text("def witness : Nat := 1\n")
    assert closure(["Solidity.First"],overlay)==["Solidity.Second","Solidity.First"]
    (overlay/"Solidity/First.lean").write_text("module\nprelude\npublic import Solidity.Second\nmeta import Solidity.Second\npublic meta import all Solidity.Second\nimport all Solidity.Second\ndef value := 0\n")
    assert imports("Solidity.First",overlay)==["Solidity.Second"]*4
    assert closure(["Solidity.First"],overlay)==["Solidity.Second","Solidity.First"]
    for prefix in ["public", "meta", "public meta", "public   meta", "public\tmeta", "public /- gap -/ meta"]:
        (overlay/"Solidity/First.lean").write_text(prefix+"\nimport Solidity.Second\n")
        try: imports("Solidity.First",overlay)
        except ValueError: pass
        else: raise AssertionError("multiline modifier silently omitted an import")
    (overlay/"Solidity/First.lean").write_text('import Solidity.«Quoted»\n')
    try: imports("Solidity.First",overlay)
    except ValueError: pass
    else: raise AssertionError("unhandled import syntax silently accepted")
    (overlay/"Solidity/First.lean").write_text("import Solidity.Missing\n")
    try: closure(["Solidity.First"],overlay)
    except ValueError: pass
    else: raise AssertionError("missing overlay import accepted")
    for name in ["one","two"]:
        subprocess.run(["python3",str(ROOT/"scripts/h62/item6/migrate-sortcheck/fixture.py"),"--out",str(pathlib.Path(td)/name)],check=True,stdout=subprocess.DEVNULL)
    a=pathlib.Path(td)/"one"; b=pathlib.Path(td)/"two"
    assert (a/"manifest.json").read_bytes()==(b/"manifest.json").read_bytes()
    patch=(a/"proposed-parser.patch").read_text()
    assert sum(line.startswith("-") and not line.startswith("---") for line in patch.splitlines())==2
    assert sum(line.startswith("+") and not line.startswith("+++") for line in patch.splitlines())==2
    for rel,digest in json.loads((a/"manifest.json").read_text()).items():
        assert hashlib.sha256((a/rel).read_bytes()).hexdigest()==digest
print("TOOLING_SELFCHECK_PASS: source freeze, 46 generated theorems, nested helper, missing-target rejection, comparison negative controls, deterministic two-line fixture")
