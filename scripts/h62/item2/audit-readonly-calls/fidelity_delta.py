#!/usr/bin/env python3
"""Diagnose upstream source drift without dropping frozen audit obligations.

This does not replace census.py's strict frozen-tree or kernel fidelity gate.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path

spec = importlib.util.spec_from_file_location("audit_census", Path(__file__).with_name("census.py"))
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)


def compare(frozen, current):
    def keyed(rows):
        result = {(r["file"], r["source_name"]): r for r in rows}
        if len(result) != len(rows):
            raise ValueError("duplicate declaration identity")
        return result
    old, new = keyed(frozen), keyed(current)
    outcomes=[]
    for key, row in sorted(old.items()):
        now = new.get(key)
        state = ("absent-upstream" if now is None else
                 "header-or-context-drift" if any(row[k] != now[k] for k in ("signature_sha256", "variable_context", "visibility")) else
                 "lexical-header-retained")
        outcomes.append({"file":key[0], "source_name":key[1], "source_status":state,
                         "frozen_signature_sha256":row["signature_sha256"],
                         "original_audit_status":row["witness_status"], "owner":row["owner"]})
    return {"original_declarations":len(old), "original_obligations":outcomes,
            "source_statuses":dict(Counter(r["source_status"] for r in outcomes)),
            "added_declarations":[{"file":k[0],"source_name":k[1]} for k in sorted(new.keys()-old.keys())],
            "boundary":"Lexical source accounting only; retained headers do not establish current kernel type, imported-definition meaning, witnesses or compiler adequacy. Absence is pending migration, never an exclusion."}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frozen",type=Path,required=True)
    parser.add_argument("--frozen-sha256",required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    raw=args.frozen.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=args.frozen_sha256:
        parser.error("frozen artifact hash mismatch")
    frozen=json.loads(raw)
    if frozen["base"]!=census.BASE or frozen["theorem_count"]!=792 or len(frozen["declarations"])!=792:
        parser.error("wrong frozen audit base or membership")
    paths=[r["file"] for r in frozen["modules"]]
    if len(paths)!=129 or len(set(paths))!=129:
        parser.error("wrong frozen module membership")
    current=[row for path in paths for row in census.declarations(path)]
    result=compare(frozen["declarations"],current)
    result.update(schema=1,base=census.BASE,frozen_artifact_sha256=args.frozen_sha256,
                  changed_modules=[row["file"] for row in frozen["modules"] if hashlib.sha256((census.ROOT/row["file"]).read_bytes()).hexdigest()!=row["sha256"]],
                  current_kernel_fidelity="pending; no Lean executed",strict_frozen_gate="not bypassed")
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"original":result["original_declarations"],"source_statuses":result["source_statuses"],"changed_modules":result["changed_modules"]}))
    return 1 if result["changed_modules"] or any(r["source_status"]!="lexical-header-retained" for r in result["original_obligations"]) else 0


if __name__=="__main__":
    raise SystemExit(main())
