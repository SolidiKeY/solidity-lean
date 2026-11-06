#!/usr/bin/env python3
"""Map every pinned corpus dependency to its assigned migration overlay owner."""
import fnmatch,hashlib,json,pathlib,sys
census=json.loads(pathlib.Path(sys.argv[1]).read_text()); ownership=pathlib.Path(sys.argv[2])
lanes=[x for x in json.loads(ownership.read_text())["items"] if x.get("id", "").startswith("H62-6-MIGRATE-")]
rows=[]
for module in census["external_dependencies"]:
    path=module.replace(".","/")+".lean"
    owners=[x["owner"] for x in lanes if any(fnmatch.fnmatchcase(path,s.strip()) for s in x.get("writeScope", "").split(";"))]
    assert len(owners)==1,(path,owners)
    rows.append(dict(module=module,path=path,migration_owner=owners[0]))
result=dict(base=census["base"],ownership_sha256=hashlib.sha256(ownership.read_bytes()).hexdigest(),
 direct_external_imports=sorted({i for f in census["files"] for i in f["imports"] if not i.startswith("Solidity.Corpus.")}),dependencies=rows)
if len(sys.argv)>4:
    extra=json.loads(pathlib.Path(sys.argv[4]).read_text())["root_extra_modules"]
    result["validation_root_extra_dependencies"]=[dict(module=m,path=m.replace(".","/")+".lean",
        migration_owners=[x["owner"] for x in lanes if any(fnmatch.fnmatchcase(m.replace(".","/")+".lean",s.strip()) for s in x.get("writeScope", "").split(";"))]) for m in extra]
pathlib.Path(sys.argv[3]).write_text(json.dumps(result,indent=2)+"\n")
print(f"{len(rows)} dependencies mapped; no missing or ambiguous owner")
