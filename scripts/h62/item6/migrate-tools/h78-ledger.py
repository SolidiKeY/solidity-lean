#!/usr/bin/env python3
"""Static H78 evidence ledger. Never infer visibility or claim compatibility."""
import argparse, copy, hashlib, json
from pathlib import Path

def validate(ledger):
    rows = ledger["declarations"]
    names = [(r["module"], r["name"]) for r in rows]
    if len(names) != len(set(names)): raise ValueError("duplicate declaration")
    if len(rows) != ledger["expected_declaration_count"]: raise ValueError("incomplete declaration coverage")
    for shim in ledger["implemented_shims"]:
        for field in ["name", "old_signature", "new_signature", "shim_signature"]:
            if not shim.get(field): raise ValueError("incomplete actual shim: " + field)
    if ledger["compatibility_established"]:
        raise ValueError("static old-only ledger cannot establish compatibility")

def build(snapshot, working_baseline):
    rows = []
    for module in snapshot["modules"]:
        for declaration in module["declarations"]:
            rows.append({"module": module["module"], "name": declaration["name"],
                "old_signature": {"level_params": copy.deepcopy(declaration["level_params"]), "type_expr": declaration["type_expr"]},
                "old_signature_format": "Lean Expr repr (ordered forallE binders) plus universe parameters",
                "old_interface_repr_sha256": declaration["interface_repr_sha256"],
                "old_kind": "theorem" if declaration["is_theorem"] else None,
                "old_is_unsafe": declaration["is_unsafe"],
                "old_visibility": None, "new_signature": None, "new_kind": None,
                "new_visibility": None, "shim_signature": None,
                "state": "missing visibility/new export evidence; no compatibility acceptance"})
    ledger = {"schema_version": 1, "frozen_source_base": snapshot["base"],
        "working_baseline": working_baseline, "expected_declaration_count": snapshot["kernel_declaration_count"],
        "scope": "ALL recorded module-owned constants, including private/generated; no generated-family exclusions",
        "source_boundary": "Historical pinned old snapshot, not revalidated against working baseline; visibility and non-theorem kinds were not captured",
        "compatibility_established": False, "implemented_shims": [],
        "declarations": sorted(rows, key=lambda r: (r["module"], r["name"]))}
    validate(ledger)
    return ledger

if __name__ == "__main__":
    parser = argparse.ArgumentParser(); parser.add_argument("--snapshot", type=Path, required=True); parser.add_argument("--working-baseline", required=True); parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(); data = build(json.loads(args.snapshot.read_text()), args.working_baseline)
    data["input"] = {"path": str(args.snapshot.resolve()), "sha256": hashlib.sha256(args.snapshot.read_bytes()).hexdigest()}
    args.output.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"declarations": len(data["declarations"]), "compatibility_established": False, "implemented_shims": []}))
