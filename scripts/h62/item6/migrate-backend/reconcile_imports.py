#!/usr/bin/env python3
"""Reconcile the source census with compiler .ilean directImports, without Lean."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from census import imports, is_toolchain_module

ROOT = Path(__file__).resolve().parents[4]

def reconcile(census, artifacts, source_root=ROOT):
    assigned = {row["module"]:row for row in census["files"]}
    actual_sources = {str(path.relative_to(source_root).with_suffix("")).replace("/", ".")
              for path in (source_root/"Solidity/Backend").rglob("*.lean")}
    if len(assigned) != len(census["files"]) or set(assigned) != actual_sources:
        raise ValueError("census omits, duplicates or adds assigned source modules")
    order = census["topological_closure"]
    if len(order) != len(set(order)) or not actual_sources.issubset(order):
        raise ValueError("closure omits or duplicates assigned source modules")
    source_imports = {}
    for module in order:
        source = source_root/(module.replace(".","/")+".lean")
        raw = source.read_bytes()
        source_imports[module] = imports(raw.decode())
        if module in assigned:
            row = assigned[module]
            if row["path"] != str(source.relative_to(source_root)) or hashlib.sha256(raw).hexdigest() != row["sha256"] or source_imports[module] != row["imports"]:
                raise ValueError("stale source census: " + module)
    positions = {module:index for index,module in enumerate(order)}
    reached = set()
    def visit(module):
        if module in reached: return
        reached.add(module)
        for dep in source_imports[module]:
            local = source_root/(dep.replace(".","/")+".lean")
            if local.is_file():
                if dep not in positions or positions[dep] >= positions[module]:
                    raise ValueError("missing dependency or invalid topological order: " + dep)
                visit(dep)
            elif not is_toolchain_module(dep):
                raise ValueError("unresolved non-toolchain dependency: " + dep)
    for module in sorted(actual_sources): visit(module)
    if reached != set(order): raise ValueError("closure contains unreachable padding modules")
    missing, unreadable, mismatches, checked = [], [], [], []
    for module in census["topological_closure"]:
        path = artifacts/(module.replace(".","/")+".ilean")
        if not path.exists():
            missing.append(module)
            continue
        try:
            data = json.loads(path.read_text())
        except (OSError,ValueError) as exc:
            unreadable.append({"module":module,"error":str(exc)})
            continue
        direct = data.get("directImports")
        if data.get("module") != module or not isinstance(direct,list) or not all(isinstance(item,list) and item and isinstance(item[0],str) for item in direct):
            mismatches.append({"module":module,"error":"unexpected compiler import metadata schema or module identity"})
            continue
        expected = source_imports[module]
        compiler_imports = [item[0] for item in direct]
        if compiler_imports != expected:
            mismatches.append({"module":module,"expected_source_imports":expected,"actual_compiler_imports":compiler_imports})
        checked.append({"module":module,"compiler_schema_version":data.get("version"),"source_imports":expected,"compiler_imports_raw":direct})
    status = "fail" if mismatches else "pending" if missing or unreadable else "pass"
    return {"schema":1,"status":status,"expected_modules":len(census["topological_closure"]),
            "checked_modules":len(checked),"source_inventory_checked":len(actual_sources),"missing":missing,"unreadable":unreadable,"mismatches":mismatches,"checked":checked,
            "boundary":"Compiler import metadata reconciliation only; incomplete artifacts cannot pass. Does not establish artifact freshness/toolchain provenance, import visibility/meta flags, kernel type/API compatibility or semantic equivalence."}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--census",type=Path,required=True)
    parser.add_argument("--artifacts",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--source-root",type=Path,default=ROOT,
                        help="Exact source checkout for this census, independent of the tooling checkout")
    args = parser.parse_args()
    census = json.loads(args.census.read_text())
    source_root = args.source_root.resolve()
    git_root = Path(subprocess.check_output(["git","rev-parse","--show-toplevel"],cwd=source_root,text=True).strip()).resolve()
    if git_root != source_root: raise ValueError("source root must be the checkout root")
    subprocess.run(["git","diff","--exit-code",census["base"],"--","Solidity"],cwd=source_root,check=True)
    result = reconcile(census,args.artifacts,source_root=source_root)
    result["source_root"] = str(source_root)
    result["source_head"] = subprocess.check_output(["git","rev-parse","HEAD"],cwd=source_root,text=True).strip()
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:result[key] for key in ("status","expected_modules","checked_modules")}))
    raise SystemExit(0 if result["status"] == "pass" else 1 if result["status"] == "fail" else 2)
