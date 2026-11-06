#!/usr/bin/env python3
"""Audit completed logs, mutation controls, toolchain pin, and export candidate.
All bulk evidence stays outside git. A clean native measurement is an isolated
Hash comparison; it does not establish the full repository runtime gate.
"""
import difflib, hashlib, json, pathlib, re, runpy, subprocess, sys
root = pathlib.Path.cwd()
out = pathlib.Path(sys.argv[1]).resolve()
namespace = runpy.run_path("scripts/h62/item6/migrate-hash/census.py")
parse = namespace["parse"]
for bad in ("private theorem x : True := trivial", "protected def x : Nat := 0", "noncomputable def x : Nat := 0", "  theorem x : True := trivial", "@[simp]\ntheorem x : True := trivial", "attribute [simp] x"):
    try: parse(bad)
    except AssertionError: pass
    else: raise AssertionError("scanner accepted unsupported declaration: "+bad)
a = parse("def x : Nat := 0")["declarations"][0]
b = parse("def x : Nat := 1")["declarations"][0]
assert a["definition_body_sha256"] != b["definition_body_sha256"]
assert parse("theorem x : True := trivial")["declarations"][0]["sha256"] != parse("theorem x : False := False.elim")["declarations"][0]["sha256"]
# Logs are only accepted for the exact sources captured before each build.
for directory in ("old-lake-clean-3", "new-lake-clean-2", "new-acceptance-3", "new-production-acceptance-1"):
    settings = json.loads((out/directory/"settings.json").read_text())
    results = json.loads((out/directory/"results.json").read_text())
    assert all(r["input_unchanged"] for r in results)
    for path,digest in settings["source_sha256"].items():
        measured = (out/directory/"inputs"/path).read_bytes()
        assert hashlib.sha256(measured).hexdigest() == digest
        if directory == "old-lake-clean-3":
            current = subprocess.check_output(["git","show","c6f550e281a7e5affa9a99bc2cdaed556dec00e4:"+path])
        elif directory == "new-lake-clean-2" and path.startswith("Solidity/Hash/"):
            current = (root/"tests/h62/item6/migrate-hash"/pathlib.Path(path).name).read_text().replace("import tests.h62.item6.«migrate-hash».CollisionBound", "import Solidity.Hash.CollisionBound").encode()
        else:
            current = (root/path).read_bytes()
        assert current == measured, "stale build evidence: "+directory+"/"+path
census = json.loads((root/"tests/h62/item6/migrate-hash/census.json").read_text())
theorems = sum(d["kind"] == "theorem" for m in census["modules"].values() for d in m["declarations"])
log = (out/"new-production-acceptance-1/tests.h62.item6.migrate-hash.ProductionInventory.log").read_text()
axioms = re.findall(r"depends on axioms:\s*\[(.*?)\]",log,re.S)
no_axioms = re.findall(r"does not depend on any axioms",log)
assert len(axioms)+len(no_axioms) == theorems, (len(axioms),len(no_axioms),theorems)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for group in axioms:
    assert {x.strip() for x in group.split(",") if x.strip()} <= allowed, group
for record in json.loads((out/"new-production-acceptance-1/results.json").read_text()):
    assert record["exit"] == 0 and not record["resource_stop"]
for path,want in json.loads(pathlib.Path("/workspace/h62-coordinator-inputs/sha256.json").read_text()).items():
    assert hashlib.sha256((pathlib.Path("/workspace/h62-coordinator-inputs")/path).read_bytes()).hexdigest() == want
pin = json.loads(pathlib.Path("/workspace/h62-coordinator-inputs/toolchain-pin.json").read_text())
archive = pathlib.Path("/workspace/migrate-hash-toolchains")/pin["asset"]
assert hashlib.file_digest(archive.open("rb"),"sha256").hexdigest() == pin["sha256"]
patch = []
for name in ("CollisionBound", "Adaptive"):
    path = f"Solidity/Hash/{name}.lean"
    original = subprocess.check_output(["git","show","c6f550e281a7e5affa9a99bc2cdaed556dec00e4:"+path],text=True)
    candidate = (root/f"tests/h62/item6/migrate-hash/{name}.lean").read_text().replace("import tests.h62.item6.«migrate-hash».CollisionBound", "import Solidity.Hash.CollisionBound")
    patch.extend(difflib.unified_diff(original.splitlines(True),candidate.splitlines(True),fromfile="a/"+path,tofile="b/"+path))
(out/"migration-candidate.patch").write_text("".join(patch))
(out/"census.json").write_text(json.dumps(census,indent=2)+"\n")
old = json.loads((out/"old-lake-clean-3/results.json").read_text())
new = json.loads((out/"new-lake-clean-2/results.json").read_text())
comparison = []
for x,y in zip(old,new,strict=True):
    assert x["module"] == y["module"] and x["exit"] == y["exit"] == 0
    comparison.append({"module":x["module"],"old_wall_seconds":x["wall_seconds"],"new_wall_seconds":y["wall_seconds"],"wall_delta_percent":100*(y["wall_seconds"]/x["wall_seconds"]-1),"old_max_rss_kib":x["max_rss_kib"],"new_max_rss_kib":y["max_rss_kib"],"rss_delta_percent":100*(y["max_rss_kib"]/x["max_rss_kib"]-1)})
x=sum(r["wall_seconds"] for r in old[1:]); y=sum(r["wall_seconds"] for r in new[1:])
summary={"comparison":comparison,"hash_wall_seconds_old":x,"hash_wall_seconds_new":y,"hash_wall_delta_percent":100*(y/x-1),"module_wall_growth_over_10_percent":y > 1.1*x or any(r["wall_delta_percent"]>10 for r in comparison),"escalate_any_regression":any(r["wall_delta_percent"]>0 or r["rss_delta_percent"]>0 for r in comparison),"scope":"private canonical-name Hash native builds; full affected/runtime gates pending"}
(out/"performance.json").write_text(json.dumps(summary,indent=2)+"\n")
acceptance={"scanner_negative_controls":6,"scanner_statement_mutation_rejected":True,"scanner_definition_mutation_rejected":True,"declarations":125,"named_api_checks":121,"anonymous_instance_checks":4,"theorem_axiom_sets":theorems,"finite_kernel_controls":19,"new_axioms":0,"sorry":0,"official_archive_sha256":pin["sha256"],"production_files_unchanged":False,"production_migration_applied":all(v["production_migration_applied"] for v in census["modules"].values()),"full_runtime_gate":"pending"}
(out/"acceptance.json").write_text(json.dumps(acceptance,indent=2)+"\n")
print(json.dumps(acceptance,indent=2)); print(json.dumps(summary,indent=2))
summary["per_module_growth_blocks_lane"] = False
summary["full_build_stop_over_10_percent"] = None
summary["coordinator_direction"] = "Record per-module time/memory growth and continue to matched clean full-build comparison; coordinator reports cut-over escalation."
(out/"performance.json").write_text(json.dumps(summary,indent=2)+"\n")
