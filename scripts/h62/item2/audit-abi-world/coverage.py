#!/usr/bin/env python3
"""Join exact frozen census to source-hash-bound, successful Lean diagnostics.

Final --require-complete gate fails for every uncovered declaration. The source
census is reviewed for this pinned grammar; the schema extracts actual Lean
binder types. This tool does not turn external test outcomes into proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
sys.dont_write_bytecode = True
import census as canonical

root = Path(__file__).resolve().parents[4]
parser = argparse.ArgumentParser()
parser.add_argument("--evidence", type=Path, required=True)
parser.add_argument("--require-complete", action="store_true")
args = parser.parse_args()
assert not args.evidence.resolve().is_relative_to(root), "H44: evidence must be outside git"
census = json.loads((args.evidence/"census.json").read_text())
assert census["base"] == canonical.BASE
assert census["module_map"] == canonical.MAP
mapping = canonical.frozen(canonical.MAP)
assert census["module_map_sha256"] == canonical.digest(mapping)
paths = canonical.module_paths(mapping)
assert len(paths) == 24 and census["mapped_modules"] == paths
expected = [r for p in paths for r in canonical.declarations(p, canonical.frozen(p))]
assert len(expected) == 177 and census["count"] == 177
assert census["declarations"] == expected, "external census differs from regenerated frozen census"
rows = {r["name"]: dict(r) for r in census["declarations"]}
assert len(rows) == census["count"]
for path in census["mapped_modules"]:
    frozen = subprocess.check_output(["git", "show", f"{census['base']}:{path}"])
    assert (root/path).read_bytes() == frozen, f"frozen interface edited: {path}"
def checked_receipt(path):
    receipt = json.loads((args.evidence/(path.stem+".json")).read_text())
    assert receipt.get("isError") is False
    audit = receipt["_audit"]
    assert audit["tool"] == "lean_diagnostic_messages"
    assert audit["file"] == str(path)
    assert audit["arguments"]["file_path"] == str(path.relative_to(root))
    assert audit["arguments"].get("interactive") is False
    assert set(audit["arguments"]) <= {"file_path", "interactive", "timeout_s", "severity"}, "partial diagnostic selection"
    assert audit["base"] == canonical.BASE and audit["frozen_sources_clean"] is True
    assert audit["lean_version"] == "Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)"
    assert audit["lean_num_threads"] == 1
    assert audit["support_before"] == audit["support_after"]
    support_paths = {"tests/h62/item2/audit-abi-world/H62AbiWorld/WitnessSchema.lean",
        "tests/h62/item2/audit-abi-world/serial.lakefile.toml",
        "scripts/h62/item2/audit-abi-world/mcp_call.py", "scripts/h62/item2/audit-abi-world/bin/lake",
        "lean-toolchain", "lakefile.toml"}
    assert set(audit["support_before"]) == support_paths
    for support, digest in audit["support_before"].items():
        assert hashlib.sha256((root/support).read_bytes()).hexdigest() == digest, f"stale dependency: {support}"
    data = receipt["structuredContent"]["result"]
    assert data.get("success") is True and data.get("partial") is False and data.get("timed_out") is False
    assert not data.get("failed_dependencies")
    assert not any(item.get("severity") == "error" for item in data.get("items", []))
    actual_hash = hashlib.sha256(path.read_bytes()).hexdigest()
    assert audit["source_sha256"] == actual_hash == audit["after_sha256"]
    for item in data["items"]:
        message = item.get("message", "")
        if "depends on axioms:" in message:
            match = re.search(r"depends on axioms: \[([^\]]*)\]", message)
            assert match
            axioms = {a.strip() for a in match[1].split(",") if a.strip()}
            assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, message
    return data, actual_hash

schema = root/"tests/h62/item2/audit-abi-world/H62AbiWorld/WitnessSchema.lean"
checked_receipt(schema)
checked = {}
for path in sorted(schema.parent.glob("*Witnesses.lean")):
    data, actual_hash = checked_receipt(path)
    for label, original in re.findall(r"theorem\s+(\w+)\s*:\s*hypotheses%\s+([\w.]+)", path.read_text()):
        assert original in rows, f"out-of-census declaration: {original}"
        assert original not in checked, f"duplicate witness accounting: {original}"
        reports = [i["message"] for i in data["items"] if i.get("severity") == "info" and re.search(r"[.]"+re.escape(label)+r"'", i.get("message", ""))]
        assert len(reports) == 1 and "axioms" in reports[0], (original, reports)
        assert "sorryAx" not in reports[0], reports[0]
        checked[original] = dict(label=label, module=str(path.relative_to(root)), source_sha256=actual_hash,
                                 receipt=path.stem+".json", axiom_report=reports[0])
for name, row in rows.items():
    row["simultaneous_witness"] = checked.get(name, "uncovered")
uncovered = [dict(name=name, owner=row["owner"]) for name,row in rows.items() if name not in checked]
report = dict(base=census["base"], mapped_modules=len(census["mapped_modules"]), total=len(rows),
              witnessed=len(checked), uncovered_count=len(uncovered), uncovered=uncovered,
              declarations=list(rows.values()), all_frozen_sources_unchanged=True,
              final_gate_complete=not uncovered,
              boundary="Binder-package feasibility only; supported-program success and gas/fork gates are separate.")
output = args.evidence/"coverage.json"
output.write_text(json.dumps(report, indent=2, ensure_ascii=False)+"\n")
print(json.dumps({k:v for k,v in report.items() if k not in ("declarations","uncovered")}))
if args.require_complete and uncovered: raise SystemExit(2)
