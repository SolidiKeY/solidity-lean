#!/usr/bin/env python3
"""Deterministically summarize completed old build manifests/types and timings."""
import collections,hashlib,json,pathlib,re,sys
out=pathlib.Path(sys.argv[1]);c=json.loads((out/"census.json").read_text());ir=out/"build-old/ir"
actual=set()
for f in c["files"]:
    a=json.loads((ir/(f["path"][:-5]+".setup.json")).read_text());actual.add(a["name"]);actual.update(a["importArts"])
assert actual==set(c["closure"]),"compiler/source census mismatch"
root=json.loads((ir/"SolidityCorpus.setup.json").read_text())
def save(name,value): (out/name).write_text(json.dumps(value,indent=2,sort_keys=True)+"\n")
save("compiler-census-crosscheck.json",dict(match=True,scoped_module_count=len(actual),root_import_count=len(root["importArts"]),root_extra_modules=sorted(set(root["importArts"])-actual)))
raw=(out/"interfaces-old.jsonl").read_bytes();rows=[json.loads(x) for x in raw.decode().splitlines()]
assert len(rows)==len({x["name"] for x in rows}) and len({x["module"] for x in rows})==9
save("interface-hashes-old.json",{x["name"]:hashlib.sha256(json.dumps(x,sort_keys=True,separators=(",",":")).encode()).hexdigest() for x in rows})
save("interface-summary-old.json",dict(constants=len(rows),by_module=dict(collections.Counter(x["module"] for x in rows)),whole_jsonl_sha256=hashlib.sha256(raw).hexdigest(),cross_version_comparison="blocked: new dependencies do not compile"))
log=(out/"clean-old-retry/output.log").read_text()
times=[dict(module=m,seconds=float(t)/(1000 if unit=="ms" else 1)) for m,t,unit in re.findall(r"^.*?\[\d+/\d+\] Built (\S+) \(([\d.]+)(ms|s)\)",log,re.M)]
assert times
save("module-timings-old.json",dict(modules=times,maximum=max(times,key=lambda x:x["seconds"]),over_300_seconds=[x for x in times if x["seconds"]>300]))
print(json.dumps(dict(compiler_census_match=True,constants=len(rows),timed_modules=len(times),maximum=max(times,key=lambda x:x["seconds"]))))
