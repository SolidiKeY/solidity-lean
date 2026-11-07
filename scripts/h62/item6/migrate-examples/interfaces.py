#!/usr/bin/env python3
"""Validate complete loaded interface sets; hashes are evidence, not semantic proofs."""
import argparse,hashlib,json,pathlib
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
SENTINELS={"Solidity.Examples.SourceCounterexample":["Solidity.Examples.SourceCounterexample.badRefuted"],"Solidity.Examples.Tactics.Step":["Solidity.Examples.Tactics.Step.reads","Solidity.Examples.Tactics.Step.writes"]}

def canonical(x):return json.dumps(x,sort_keys=True,separators=(",",":"),ensure_ascii=True).encode()
def digest(x):return hashlib.sha256(canonical(x)).hexdigest()
def check_closed(tree):
    stack=[tree]
    while stack:
        item=stack.pop()
        if isinstance(item,list):
            if item and isinstance(item[0],str) and item[0].startswith("unexpected-"):raise ValueError("open declaration type")
            stack.extend(item)

def inventory(raw,census):
    if census["base"]!=BASE:raise ValueError("wrong pinned base")
    expected={m["module"] for m in census["modules"]}
    if len(expected)!=len(census["modules"]):raise ValueError("duplicate census module")
    lines=iter(raw.splitlines() if isinstance(raw,str) else raw);header=json.loads(next(lines))
    if header.get("schema")!="h62-examples-interface-v1":raise ValueError("wrong schema")
    actual=header["modules"]
    if len(actual)!=len(set(actual)) or set(actual)!=expected:raise ValueError("incomplete or unexpected module inventory")
    counts={m:0 for m in sorted(expected)};decls={};seen=set();complete=False
    for line in lines:
        if not line.strip():continue
        row=json.loads(line)
        if complete:raise ValueError("data after completion footer")
        if "complete" in row:
            if row.get("complete") is not True or type(row.get("declarations")) is not int or row["declarations"]!=len(decls):raise ValueError("invalid completion footer")
            complete=True;continue
        module=row["module"]
        if module not in expected:raise ValueError("declaration outside scope")
        if not isinstance(row["name_key"],list) or not isinstance(row["type"],list) or not row["type"]:raise ValueError("missing structural identity/type")
        if any(type(row.get(field)) is not bool for field in ("private_name", "protected_name")):raise ValueError("missing or invalid visibility-name flags")
        check_closed(row["type"])
        name_key=canonical(row["name_key"]).decode()
        if name_key in seen:raise ValueError("duplicate declaration identity")
        seen.add(name_key)
        frozen={key:row[key] for key in ("module","name_key","kind","unsafe","level_parameters","type","private_name","protected_name")}
        identity=canonical([module,row["name_key"]]).decode()
        decls[identity]={"name":row["name"],"module":module,"type_sha256":digest(frozen),"kind":row["kind"],"private_name":row["private_name"],"protected_name":row["protected_name"]}
        counts[module]+=1
    if not complete:raise ValueError("missing completion footer")
    if not decls:raise ValueError("empty declaration inventory")
    for module,names in SENTINELS.items():
        if module not in expected:continue
        for name in names:
            key=["anonymous"]
            for part in name.split("."):key=["str",key,part]
            if canonical([module,key]).decode() not in decls:raise ValueError("missing generated sentinel: "+name)
    entries={key:decls[key] for key in sorted(decls)}
    return {"schema":"h62-examples-frozen-v1","base":census["base"],"modules":sorted(expected),"module_counts":counts,"declarations":entries,"interface_sha256":digest({"base":census["base"],"modules":sorted(expected),"types":{k:v["type_sha256"] for k,v in entries.items()}}),"source_blobs":{r["path"]:r["source_sha256"] for r in census["modules"]},"boundary":"loaded named constants including imported generated/private constants when available; anonymous command cases require source census and successful full builds; fingerprints include private/protected-name flags but do not prove complete module-export visibility or definition-semantic equivalence"}

def compare(old,new):
    if old["base"]!=new["base"] or old["modules"]!=new["modules"]:raise ValueError("different frozen scope/base")
    a=old["declarations"];b=new["declarations"]
    return {"removed":sorted(set(a)-set(b)),"added":sorted(set(b)-set(a)),"changed":sorted(k for k in set(a)&set(b) if a[k]["type_sha256"]!=b[k]["type_sha256"])}

def main():
    p=argparse.ArgumentParser();p.add_argument("--raw",type=pathlib.Path,required=True);p.add_argument("--census",type=pathlib.Path,required=True);p.add_argument("--output",type=pathlib.Path,required=True);p.add_argument("--compare",type=pathlib.Path);a=p.parse_args()
    census=json.loads(a.census.read_text())
    if len(census["modules"])!=354:raise ValueError("expected all 354 assigned modules")
    with a.raw.open() as stream:data=inventory(stream,census)
    a.output.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"modules":len(data["modules"]),"declarations":len(data["declarations"]),"interface_sha256":data["interface_sha256"]}))
    if a.compare:
        delta=compare(json.loads(a.compare.read_text()),data);print(json.dumps(delta));return int(any(delta.values()))
    return 0
if __name__=="__main__":raise SystemExit(main())
