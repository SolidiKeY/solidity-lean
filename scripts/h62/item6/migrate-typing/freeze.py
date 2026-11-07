#!/usr/bin/env python3
"""Hash all elaborated old interfaces and source identities; emit bulk off Git."""
import argparse, hashlib, json, pathlib

def sha(data): return hashlib.sha256(data).hexdigest()
def encode(data): return json.dumps(data,sort_keys=True,separators=(",", ":")).encode()
def freeze(census,api):
    expected={f["module"] for f in census["files"]}
    if {entry["module"] for entry in api}!=expected: raise ValueError("API module coverage mismatch")
    names=[entry["name"] for entry in api]
    if len(names)!=len(set(names)): raise ValueError("duplicate constant")
    if any("sorryAx" in entry["axioms"] for entry in api): raise ValueError("sorryAx in frozen API")
    entries=[]
    for entry in sorted(api,key=lambda e:e["name"]):
        statement={k:entry[k] for k in ("module","name","levelParams","typeExpr")}
        entries.append({"module":entry["module"],"name":entry["name"],"statement_sha256":sha(encode(statement)),"axioms":entry["axioms"]})
    return {"schema":1,"baseline_toolchain":"leanprover/lean4:v4.24.0","base":census["base"],"source_sha256":{f["path"]:f["sha256"] for f in census["files"]},"constants":entries,"aggregate_statement_sha256":sha(encode(entries)),"limitation":"old elaborated baseline only; new environment is blocked by Syntax.Raw; no cross-version equality claimed"}
if __name__=="__main__":
    ap=argparse.ArgumentParser();ap.add_argument("census",type=pathlib.Path);ap.add_argument("api",type=pathlib.Path);a=ap.parse_args()
    print(json.dumps(freeze(json.loads(a.census.read_text()),json.loads(a.api.read_text())),sort_keys=True,indent=2))
