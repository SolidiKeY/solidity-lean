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
from receipts import checked_receipt as validate_receipt

def checked_receipt(path):
    return validate_receipt(path,args.evidence)

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
                                 receipt=path.stem+".json", qualified_name=re.match(r"'([^']+)'",reports[0])[1], axiom_report=reports[0])
fidelity_path = schema.parent/"Fidelity.lean"
fidelity_data,_ = checked_receipt(fidelity_path)
fidelity_receipt = json.loads((args.evidence/"Fidelity.json").read_text())
local_dependencies = {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted(schema.parent.glob("*.lean"))}
assert fidelity_receipt["_fidelity_dependencies"]["before"] == local_dependencies
assert fidelity_receipt["_fidelity_dependencies"]["after"] == local_dependencies
fidelity = {}
for item in fidelity_data["items"]:
    if not item.get("message", "").startswith("FIDELITY "): continue
    record = json.loads(item["message"][len("FIDELITY "):])
    name=record["original"]
    assert name in rows and name not in fidelity, "duplicate or unknown fidelity statement"
    assert record["matched"] is True, "fidelity mismatch"
    assert name in checked and record["witness"] == checked[name]["qualified_name"]
    assert record["binder_count"] == len(record["binders"])
    assert record["original_type"] and record["witness_type"]
    assert all(type(b["proposition"]) is bool for b in record["binders"])
    fidelity[name]=record
assert set(fidelity) == set(rows), "missing fidelity statements"
for name, row in rows.items():
    row["simultaneous_witness"] = checked.get(name, "uncovered")
    row["elaborated_fidelity"] = fidelity[name]
uncovered = [dict(name=name, owner=row["owner"]) for name,row in rows.items() if name not in checked]
report = dict(base=census["base"], mapped_modules=len(census["mapped_modules"]), total=len(rows),
              witnessed=len(checked), uncovered_count=len(uncovered), uncovered=uncovered,
              fidelity_statements=len(fidelity), binder_count=sum(r["binder_count"] for r in fidelity.values()),
              proposition_binders=sum(b["proposition"] for r in fidelity.values() for b in r["binders"]),
              proposition_premise_statements=sum(any(b["proposition"] for b in r["binders"]) for r in fidelity.values()),
              data_only_statements=sum(r["binder_count"] > 0 and not any(b["proposition"] for b in r["binders"]) for r in fidelity.values()),
              binder_free_statements=sum(r["binder_count"] == 0 for r in fidelity.values()),
              declarations=list(rows.values()), all_frozen_sources_unchanged=True,
              witness_gate_complete=not uncovered and len(fidelity)==len(rows),
              assignment_complete=False,
              boundary="Binder-package feasibility and type fidelity only; success/gas/fork and final validation are separate gates.")
output = args.evidence/"coverage.json"
output.write_text(json.dumps(report, indent=2, ensure_ascii=False)+"\n")
print(json.dumps({k:v for k,v in report.items() if k not in ("declarations","uncovered")}))
if args.require_complete and not report["witness_gate_complete"]: raise SystemExit(2)
