#!/usr/bin/env python3
"""Prepare and hash structural Lean type exports; compiler validation is separate."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
TEMPLATE = ROOT/"tests/h62/item6/migrate-backend/ApiInventory.lean.in"

def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":")).encode()

def natural_ok(value):
    return isinstance(value,str) and (value == "0" or bool(value) and value[0] in "123456789" and all(c in "0123456789" for c in value))

def name_ok(name):
    if name == ["anonymous"]: return True
    if not isinstance(name,list) or len(name) != 3 or not name_ok(name[1]): return False
    if name[0] == "str": return isinstance(name[2],str)
    if name[0] == "num": return natural_ok(name[2])
    return False

def name_is_private(name):
    if name == ["anonymous"]: return False
    return name == ["str",["anonymous"],"_private"] or name_is_private(name[1])

def visibility_ok(row):
    expected = "private" if name_is_private(row["name"]) else "public"
    return row.get("visibility") == expected and type(row.get("protected")) is bool

def level_ok(level):
    if level == ["zero"]: return True
    if not isinstance(level,list) or not level: return False
    if level[0] == "succ": return len(level) == 2 and level_ok(level[1])
    if level[0] in ("max","imax"):
        return len(level) == 3 and level_ok(level[1]) and level_ok(level[2])
    if level[0] == "param": return len(level) == 2 and name_ok(level[1])
    return False

def type_hash(dag):
    nodes, root = dag["nodes"], dag["root"]
    if not nodes or type(root) is not int or root != len(nodes)-1:
        raise ValueError("malformed type DAG root")
    hashes, loose, edges = [], [], []
    for position, node in enumerate(nodes):
        if not isinstance(node,list) or not node or not isinstance(node[0],str):
            raise ValueError("malformed type DAG node")
        tag = node[0]
        children = []
        def child(index):
            if type(index) is not int or not 0 <= index < position:
                raise ValueError("DAG child must precede its parent")
            children.append(index)
            return hashes[index]
        def natural(value):
            if not natural_ok(value): raise ValueError("invalid natural")
            return int(value)
        if tag == "bvar" and len(node) == 2:
            data, free = node, natural(node[1])+1
        elif tag == "sort" and len(node) == 2 and level_ok(node[1]):
            data, free = node, 0
        elif tag == "const" and len(node) == 3 and name_ok(node[1]) and isinstance(node[2],list) and all(level_ok(x) for x in node[2]):
            data, free = node, 0
        elif tag == "app" and len(node) == 3:
            data = [tag,child(node[1]),child(node[2])]
            free = max(loose[x] for x in children)
        elif tag in ("lam","forallE") and len(node) == 5 and name_ok(node[1]) and node[4] in ("default","implicit","strictImplicit","instImplicit"):
            data = [tag,node[1],child(node[2]),child(node[3]),node[4]]
            free = max(loose[node[2]],max(0,loose[node[3]]-1))
        elif tag == "letE" and len(node) == 6 and name_ok(node[1]) and type(node[5]) is bool:
            data = [tag,node[1],child(node[2]),child(node[3]),child(node[4]),node[5]]
            free = max(loose[node[2]],loose[node[3]],max(0,loose[node[4]]-1))
        elif tag == "natVal" and len(node) == 2:
            natural(node[1]);data,free = node,0
        elif tag == "strVal" and len(node) == 2 and isinstance(node[1],str):
            data,free = node,0
        elif tag == "mdata" and len(node) == 2:
            data = child(node[1]);free = loose[node[1]]
        elif tag == "proj" and len(node) == 4 and name_ok(node[1]):
            natural(node[2]);data = [tag,node[1],node[2],child(node[3])];free = loose[node[3]]
        else:
            raise ValueError("unsupported or open kernel expression node")
        hashes.append(data if tag == "mdata" else hashlib.sha256(canonical(data)).hexdigest())
        loose.append(free);edges.append(children)
    if loose[root]: raise ValueError("loose bound variable in exported kernel type")
    seen, pending = set(), [root]
    while pending:
        index = pending.pop()
        if index in seen: continue
        seen.add(index);pending.extend(edges[index])
    if len(seen) != len(nodes): raise ValueError("unreachable nodes in type DAG")
    return hashes[root]

def universe_parameters(dag):
    found = set()
    def visit(level):
        if level[0] == "param": found.add(canonical(level[1]))
        elif level[0] == "succ": visit(level[1])
        elif level[0] in ("max","imax"):
            visit(level[1]);visit(level[2])
    for node in dag["nodes"]:
        if node[0] == "sort": visit(node[1])
        elif node[0] == "const":
            for level in node[2]: visit(level)
    return found

def validate_index(index):
    modules = index.get("modules")
    rows = index.get("declarations")
    if type(index.get("schema")) is not int or index["schema"] != 2 or not isinstance(modules,list) or any(not isinstance(x,str) for x in modules) or len(set(modules)) != len(modules):
        raise ValueError("invalid index module inventory")
    if not isinstance(rows,list) or type(index.get("declaration_count")) is not int or index["declaration_count"] != len(rows):
        raise ValueError("invalid index declaration count")
    def digest(value):
        return isinstance(value,str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)
    if not digest(index.get("raw_sha256")): raise ValueError("invalid raw export digest")
    names = set()
    for row in rows:
        if set(row) != {"name","display_name","module","kind","level_params","unsafe","visibility","protected","type_sha256"}:
            raise ValueError("invalid indexed declaration fields")
        if not name_ok(row["name"]) or not isinstance(row["display_name"],str) or row["module"] not in modules or not digest(row["type_sha256"]):
            raise ValueError("invalid indexed declaration identity or type digest")
        if row["kind"] not in {"axiom","definition","theorem","opaque","quotient","inductive","constructor","recursor"} or type(row["unsafe"]) is not bool:
            raise ValueError("invalid indexed declaration kind")
        if not visibility_ok(row): raise ValueError("invalid or inconsistent visibility metadata")
        params = row["level_params"]
        if not isinstance(params,list) or not all(name_ok(x) for x in params) or len({canonical(x) for x in params}) != len(params):
            raise ValueError("invalid or duplicate universe parameters")
        key = canonical(row["name"])
        if key in names: raise ValueError("duplicate indexed declaration name")
        names.add(key)
    return index

def validate_output(path, inputs=()):
    path = path.resolve()
    allowed = (ROOT/"tests/h62/item6/migrate-backend",Path("/workspace/migrate-backend-evidence"))
    if not any(path.is_relative_to(folder.resolve()) for folder in allowed):
        raise ValueError("output outside assigned tests/evidence scope")
    if path in {p.resolve() for p in inputs} or path.exists():
        raise ValueError("refusing output alias or existing output")
    return path

def index_export(raw, census):
    expected = {entry["module"] for entry in census["files"]}
    entries = {}
    with raw.open() as stream:
        header = json.loads(next(stream))
        modules = header.get("module_inventory", [])
        if type(header.get("schema")) is not int or header["schema"] != 2 or len(set(modules)) != len(modules) or set(modules) != expected:
            raise ValueError("export module inventory does not match assigned census")
        for line in stream:
            row = json.loads(line)
            if row["module"] not in expected:
                raise ValueError("declaration outside assigned module census")
            if set(row) != {"name","display_name","module","kind","level_params","unsafe","visibility","protected","type"}:
                raise ValueError("unexpected declaration record fields")
            if not name_ok(row["name"]) or not isinstance(row["display_name"],str) or type(row["unsafe"]) is not bool:
                raise ValueError("invalid declaration metadata")
            if not visibility_ok(row): raise ValueError("invalid or inconsistent visibility metadata")
            if row["kind"] not in {"axiom","definition","theorem","opaque","quotient","inductive","constructor","recursor"}:
                raise ValueError("unknown kernel declaration kind")
            if not isinstance(row["level_params"],list) or not all(name_ok(x) for x in row["level_params"]):
                raise ValueError("invalid declaration universe parameters")
            parameters = {canonical(x) for x in row["level_params"]}
            if len(parameters) != len(row["level_params"]): raise ValueError("duplicate universe parameters")
            key = canonical(row["name"]).decode()
            if key in entries:
                raise ValueError("duplicate structural declaration name")
            closed_type = row.pop("type")
            row["type_sha256"] = type_hash(closed_type)
            if not universe_parameters(closed_type) <= parameters:
                raise ValueError("undeclared universe parameter in exported type")
            entries[key] = row
    if type(header.get("declaration_count")) is not int or header["declaration_count"] != len(entries):
        raise ValueError("declaration count mismatch")
    with raw.open("rb") as stream: raw_sha256 = hashlib.file_digest(stream,"sha256").hexdigest()
    return {"schema": 2, "modules": sorted(expected),
            "declaration_count": len(entries),
            "raw_sha256": raw_sha256,
            "boundary": "Includes every exported declaration, including private/generated names; private/public naming and protected metadata are retained. Type hashes are sharing-independent Merkle hashes; expression metadata only is omitted. Not semantic equivalence, axiom auditing or a compiler gate.",
            "declarations": [entries[key] for key in sorted(entries)]}

def compare(old, new):
    validate_index(old);validate_index(new)
    before = {canonical(row["name"]).decode():row for row in old["declarations"]}
    after = {canonical(row["name"]).decode():row for row in new["declarations"]}
    return {"missing_modules": sorted(set(old["modules"])-set(new["modules"])),
            "extra_modules": sorted(set(new["modules"])-set(old["modules"])),
            "missing": [before[key] for key in sorted(before.keys()-after.keys())],
            "extra": [after[key] for key in sorted(after.keys()-before.keys())],
            "changed": [{"old":before[key],"new":after[key]}
                        for key in sorted(before.keys() & after.keys()) if before[key] != after[key]],
            "boundary": "No private/generated declarations are silently excluded; all differences require classification."}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="action",required=True)
    prepare = sub.add_parser("prepare")
    prepare.add_argument("--output", type=Path, required=True)
    prepare.add_argument("--raw-output", type=Path, required=True)
    controls = sub.add_parser("prepare-controls")
    controls.add_argument("--output",type=Path,required=True)
    index = sub.add_parser("index")
    index.add_argument("--raw", type=Path, required=True)
    index.add_argument("--census", type=Path, required=True)
    index.add_argument("--output", type=Path, required=True)
    diff = sub.add_parser("compare")
    diff.add_argument("--old", type=Path, required=True)
    diff.add_argument("--new", type=Path, required=True)
    diff.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    inputs = [getattr(args,key) for key in ("raw","census","old","new") if hasattr(args,key)] + [TEMPLATE]
    args.output = validate_output(args.output,inputs)
    if args.action == "prepare":
        args.raw_output = validate_output(args.raw_output,inputs+[args.output])
        validate_output(Path(str(args.raw_output)+".partial"),inputs+[args.output,args.raw_output])
    if args.action == "prepare":
        source = TEMPLATE.read_text()
        if source.count("@@OUTPUT@@") != 1:
            raise ValueError("ambiguous template output marker")
        args.output.write_text(source.replace("@@OUTPUT@@",json.dumps(str(args.raw_output.resolve()))))
        print("Prepared unverified Lean metadata exporter; run prescribed compiler/MCP validation before indexing.")
    elif args.action == "prepare-controls":
        source = TEMPLATE.read_text().split("\nrun_cmd do",1)[0].replace("import Solidity\n", "")
        source += "\nrun_cmd do\n  match structuralCacheControl with\n  | .ok () => logInfo \"Structural binder-cache control passed\"\n  | .error message => throwError \"{message}\"\n\nend MigrateBackendApiInventory\n"
        args.output.write_text(source)
        print("Prepared unverified serializer control from exact exporter template.")
    elif args.action == "index":
        result = index_export(args.raw,json.loads(args.census.read_text()))
        args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
        print(json.dumps({"declaration_count":result["declaration_count"],"raw_sha256":result["raw_sha256"]}))
    else:
        result = compare(json.loads(args.old.read_text()),json.loads(args.new.read_text()))
        args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
        changed = any(result[key] for key in ("missing_modules","extra_modules","missing","extra","changed"))
        print("DIFFERENCES_REQUIRE_REVIEW" if changed else "EXPORTED_TYPES_MATCH; compiler gates and semantics still separate")
        raise SystemExit(1 if changed else 0)
