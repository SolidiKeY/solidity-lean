#!/usr/bin/env python3
"""Canonical checked-environment inventory, not a cross-version equality proof.
Lean generator: tests/h62/item6/migrate-tools/ApiInventory.lean.
"""
import argparse, hashlib, json
from pathlib import Path

def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode()).hexdigest()

def validate_receipt(receipt, log, generator):
    if not receipt.get("passed") or receipt.get("status") != "complete": raise ValueError("inventory Lean check did not pass")
    rows = [r for r in receipt.get("modules", []) if r.get("module") == "tests.h62.item6.migrate-tools.ApiInventory"]
    if len(rows) != 1: raise ValueError("receipt has no unique inventory module")
    row = rows[0]
    if row.get("exit") != 0 or row.get("blocker") is not None: raise ValueError("inventory module did not pass")
    if Path(row["log"]).resolve() != log.resolve(): raise ValueError("receipt/log path mismatch")
    command = row.get("command", [])
    if not command: raise ValueError("receipt has no source command")
    source = Path(command[-1])
    root = Path(__file__).resolve().parents[4]
    if (source if source.is_absolute() else root / source).resolve() != generator.resolve(): raise ValueError("receipt/generator path mismatch")

def normalize(records, census):
    wanted = {r["module"]: r for r in census["modules"]}
    names = [r["module"] for r in records]
    if len(set(names)) != len(names): raise ValueError("duplicate module record")
    if set(names) != set(wanted): raise ValueError("module set does not cover exact assigned census")
    modules = []
    for record in sorted(records, key=lambda r: r["module"]):
        source = wanted[record["module"]]
        declarations = sorted(record["declarations"], key=lambda d: d["name"])
        if not declarations: raise ValueError("module has no kernel declarations")
        by_name = {d["name"]: d for d in declarations}
        if len(by_name) != len(declarations): raise ValueError("duplicate declaration")
        expected = sorted(d["source_head"].split()[0].split(".")[-1] for d in source["declaration_candidates"] if d["kind"] == "theorem")
        matched = sorted(record["source_theorems"])
        if sorted(n.split(".")[-1] for n in matched) != expected: raise ValueError("source theorem coverage mismatch")
        if any(n not in by_name or not by_name[n]["is_theorem"] for n in matched): raise ValueError("source theorem is not a recorded kernel theorem")
        all_theorems = sorted(record["module_theorems"])
        if all_theorems != sorted(d["name"] for d in declarations if d["is_theorem"]): raise ValueError("kernel theorem coverage mismatch")
        if not set(record["source_theorem_axiom_union"]) <= set(record["module_theorem_axiom_union"]): raise ValueError("inconsistent theorem axiom unions")
        for declaration in declarations:
            if not isinstance(declaration["type_expr"], str) or not declaration["type_expr"]: raise ValueError("missing type representation")
            declaration["interface_repr_sha256"] = digest({k: declaration[k] for k in ["name", "type_expr", "level_params", "is_unsafe", "is_theorem"]})
        modules.append({"module": record["module"], "path": source["path"], "source_sha256": source["sha256"],
            "interface_repr_sha256": digest([(d["name"], d["interface_repr_sha256"]) for d in declarations]),
            "declarations": declarations, "source_theorems": matched,
            "source_theorem_axiom_union": sorted(set(record["source_theorem_axiom_union"])),
            "module_theorems": all_theorems, "module_theorem_axiom_union": sorted(set(record["module_theorem_axiom_union"]))})
    return {"base": census["base"], "module_count": len(modules), "kernel_declaration_count": sum(len(m["declarations"]) for m in modules),
        "module_theorem_count": sum(len(m["module_theorems"]) for m in modules),
        "module_theorem_axiom_union": sorted(set(a for m in modules for a in m["module_theorem_axiom_union"])),
        "source_theorem_count": sum(len(m["source_theorems"]) for m in modules),
        "source_theorem_axiom_union": sorted(set(a for m in modules for a in m["source_theorem_axiom_union"])),
        "boundary": "All imported kernel constants owned by assigned modules, including private/generated constants. Type-representation hashes freeze this toolchain's representation; they are not cross-version semantic equality proofs. Source commands remain separately inventoried.", "modules": modules}

if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("--log", type=Path, required=True); ap.add_argument("--census", type=Path, required=True); ap.add_argument("--receipt", type=Path, required=True); ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    receipt = json.loads(args.receipt.read_text())
    generator = Path(__file__).resolve().parents[4] / "tests/h62/item6/migrate-tools/ApiInventory.lean"
    validate_receipt(receipt, args.log, generator)
    records = [json.loads(line) for line in args.log.read_text().splitlines() if line.strip()]
    census = json.loads(args.census.read_text())
    if census["module_count"] != 30: raise SystemExit("expected exact 30-module frozen scope")
    result = normalize(records, census); result["lean_version"] = receipt["lean_version"]; result["lake_version"] = receipt["lake_version"]
    result["inventory_check_receipt"] = str(args.receipt)
    result["provenance"] = {label: {"path": str(path.resolve()), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for label, path in [
        ("raw_log", args.log), ("source_census", args.census), ("check_receipt", args.receipt), ("generator_source", generator), ("normalizer_source", Path(__file__))]}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    print(json.dumps({k: result[k] for k in ["module_count", "kernel_declaration_count", "source_theorem_count", "source_theorem_axiom_union", "module_theorem_count", "module_theorem_axiom_union"]}))
