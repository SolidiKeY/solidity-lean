#!/usr/bin/env python3
"""Reconcile partial source, kernel and joint-proof evidence without hiding gaps."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    root, evidence = Path.cwd(), args.evidence.resolve()
    if evidence.is_relative_to(root): parser.error("H44: bulk evidence must be outside git")
    subprocess.run(["git", "diff", "--exit-code", BASE, "--", "Solidity", "docs/module-map"], check=True, stdout=subprocess.DEVNULL)
    source = json.loads((evidence/"source-census.json").read_text())
    for item in source["sources"]:
        if sha(root/item["path"]) != item["sha256"]: raise RuntimeError("stale frozen source hash")
    receipts = [json.loads(line) for line in (evidence/"baseline/lean-commands.jsonl").read_text().splitlines()]
    kernel = {}
    for path in sorted((evidence/"baseline/kernel").rglob("*.json")):
        item = json.loads(path.read_text())
        for theorem in item["theorems"]:
            name = theorem["name"]
            if name in kernel and kernel[name]["type_expression"] != theorem["type_expression"]:
                raise RuntimeError("conflicting kernel statement: "+name)
            kernel[name] = theorem
    witnesses = {}
    for file in sorted((root/"tests/h62/item2/audit-calculus").glob("*Witnesses.lean")):
        relative = str(file.relative_to(root))
        latest = [r for r in receipts if r["file"] == relative and r.get("kind") != "kernel-census"][-1]
        if latest["exit"] != 0 or latest["source_sha256"] != sha(file):
            raise RuntimeError("missing passing current-source proof receipt: "+relative)
        log = Path(latest["log"]).read_text()
        if re.search(r"\berror:|\bwarning:", log): raise RuntimeError("diagnostic errors/warnings: "+relative)
        expected = re.findall(r"^#verify_joint (\S+) with (\S+)", file.read_text(), re.M)
        verified = [json.loads(line.split("H62_JOINT_VERIFIED ",1)[1]) for line in log.splitlines() if "H62_JOINT_VERIFIED " in line]
        if len(expected) != len(verified): raise RuntimeError("joint verification count mismatch")
        for (original, short), record in zip(expected, verified):
            if record["original"] != original or record["witness"].split(".")[-1] != short:
                raise RuntimeError("joint verification identity mismatch")
            if original in witnesses: raise RuntimeError("original theorem counted twice: "+original)
            if set(record["axioms"]) - {"propext", "Classical.choice", "Quot.sound"}:
                raise RuntimeError("unexpected joint witness axiom")
            if original not in kernel or record["original_type_expression"] != kernel[original]["type_expression"]:
                raise RuntimeError("joint witness/kernel frozen statement mismatch: "+original)
            witnesses[original] = dict(record, file=relative)
    accounted = []
    for row in source["declarations"]:
        record = dict(row)
        if row["source_name"] in witnesses:
            record["joint_witness"] = witnesses[row["source_name"]]
            record["owner"] = "V14 (v12-v17/v14-payments-bytecode); producer-family key, exact-file confirmation pending"
            record["hypotheses"] = "per-input; no global compiler-correctness structure; exact telescope recorded by kernel"
            record["signature_status"] = "source candidate matched to kernel theorem type by verified joint receipt"
        accounted.append(record)
    matched = sum(isinstance(row["joint_witness"], dict) for row in accounted)
    if matched != len(witnesses): raise RuntimeError("source name collision or missing source match")
    source_names = {row["source_name"] for row in accounted}
    generated = [dict(row, status="pending generated/private/projection classification") for name,row in sorted(kernel.items()) if name not in source_names]
    result = {"base": BASE, "audit_status": "partial", "source_candidates": accounted,
              "additional_kernel_theorems": generated,
              "counts": {"source_candidates": len(accounted), "verified_source_joint_witnesses": matched,
                         "source_candidates_uncovered": len(accounted)-matched,
                         "kernel_theorems_in_exported_modules": len(kernel),
                         "additional_kernel_candidates_uncovered": len(generated)},
              "limitations": ["kernel export incomplete", "all owners require exact-file confirmation",
                              "full source compiler totality, gas/fork/world boundaries pending",
                              "full affected validation and performance gate pending"]}
    output = evidence/"acceptance.json"
    output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps({"status": "partial", "output": str(output), "sha256": sha(output), **result["counts"]}, sort_keys=True))
    if args.require_complete and (result["counts"]["source_candidates_uncovered"] or generated or result["limitations"]):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
