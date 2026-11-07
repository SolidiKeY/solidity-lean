#!/usr/bin/env python3
"""Aggregate base-pinned lexical ledgers; descriptions remain manual prose."""
import argparse, collections, json, pathlib, subprocess, sys

DIRECTORY = pathlib.Path(__file__).resolve().parent
LEDGERS = (
 "controls_ledger.py", "checked_mul_populated_ledger.py", "signed_controls_ledger.py", "checked_pipeline_ledger.py",
 "signed_mod_source_ledger.py", "signed_mod_selection_ledger.py", "signed_mod_controls_ledger.py",
 "signed_div_contract_ledger.py", "signed_div_origin_ledger.py", "signed_div_selected_ledger.py", "signed_div_execution_ledger.py", "signed_div_controls_ledger.py",
 "signed_sub_execution_ledger.py", "signed_sub_controls_ledger.py", "unsigned_div_origin_ledger.py", "unsigned_div_selection_numeric_ledger.py",
 "unsigned_div_execution_composition_ledger.py", "unsigned_div_witness_ledger.py", "private_header_ledger.py",
)
PRIVATE = "private_header_ledger.py"
FIELDS = ("file", "line", "kind", "name", "sha256")

def key(row):
    return tuple(row[field] for field in FIELDS)

def validate_census(provided, fresh):
    if provided != fresh:
        raise ValueError("supplied census differs from fresh declarations.py output")

def summarize(census, ledgers):
    original = [key(row) for row in census]
    if len(set(original)) != len(original):
        raise ValueError("duplicate original census row")
    available = set(original)
    seen = set()
    private = set()
    counts = {}
    for name, rows in ledgers:
        if name in counts:
            raise ValueError("duplicate ledger name")
        counts[name] = len(rows)
        for row in rows:
            identity = key(row)
            if identity in seen or identity in private:
                raise ValueError("overlapping or duplicate ledger row")
            if name == PRIVATE:
                if identity in available:
                    raise ValueError("private row overlaps original census")
                private.add(identity)
            else:
                if identity not in available:
                    raise ValueError("ledger row absent from original census")
                seen.add(identity)
    missing = [row for row in census if key(row) not in seen]
    return {"method": "set reconciliation of generated lexical rows; observations are manually reviewed prose and are not mechanically checked against Lean statements", "original_census": len(original), "private_rows": len(private), "observed_headers": len(original) + len(private), "described_original": len(seen), "described_private": len(private), "described_total": len(seen) + len(private), "unclassified_original": len(missing), "ledger_counts": counts, "unclassified": missing}

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--declarations", type=pathlib.Path, required=True)
    args = p.parse_args()
    census = json.loads(args.declarations.read_text())["declarations"]
    fresh = json.loads(subprocess.check_output([sys.executable, str(DIRECTORY / "declarations.py")]))["declarations"]
    validate_census(census, fresh)
    ledgers = []
    for name in LEDGERS:
        raw = subprocess.check_output([sys.executable, str(DIRECTORY / name), "--declarations", str(args.declarations)])
        ledgers.append((name, json.loads(raw)["declarations"]))
    print(json.dumps(summarize(census, ledgers), ensure_ascii=False, indent=2))

if __name__ == "__main__": main()
