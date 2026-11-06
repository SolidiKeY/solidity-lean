#!/usr/bin/env python3
"""Regression guard: conditional preservation is not compiler success/totality.

Account for every frozen lexical candidate exactly once. Only independently
reviewed roles are classified; neither missing kernel exports nor unknown owners
are silently discharged. This is static classification, not a proof gate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
EXPECTED_CENSUS = "a2aa6d5e5837eac11ad80fc4eb59e4c3903e9d7f9d52e41bcbccb1e24dccc2da"
REPO = Path(__file__).resolve().parents[4]
CURATED = REPO / "tests/h62/item2/audit-calculus/lifetime-semantic-roles.json"


def authenticated_census(path):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != EXPECTED_CENSUS:
        raise ValueError("incomplete or changed frozen census")
    return json.loads(data)


def classify(source, curated):
    declarations = source["declarations"]
    index = {row["id"]: row for row in declarations}
    if len(index) != len(declarations):
        raise ValueError("duplicate source identity")
    reviewed = {}
    for row in curated["declarations"]:
        identity = row["id"]
        if identity in reviewed or identity not in index:
            raise ValueError("duplicate or unknown reviewed identity")
        original = index[identity]
        if row["signature_sha256"] != original["signature_sha256"] or row["name"] != original["source_name"]:
            raise ValueError("classification does not match frozen signature")
        if row["file"] != original["file"] or row["line"] != original["line"]:
            raise ValueError("classification provenance differs")
        if set(row["global_proof_obligations"]) & set(row["per_input_proof_facts"]):
            raise ValueError("proof premise assigned two roles")
        reviewed[identity] = row
    expected = {row["id"] for row in declarations if row["file"] == curated["reviewed_file"]}
    if set(reviewed) != expected:
        raise ValueError("reviewed file has unaccounted declarations")
    result = []
    for original in declarations:
        row = {key: original[key] for key in ["id", "file", "line", "source_name", "signature_sha256"]}
        row["semantic_owner_status"] = "unresolved; migration scope does not establish live semantic ownership"
        if original["id"] in reviewed:
            row.update(role_status="reviewed static source classification", roles=reviewed[original["id"]])
        else:
            row["role_status"] = "pending semantic review; no premise/conclusion role inferred"
        result.append(row)
    return {"schema_version": 1, "base": source["base"], "source_census_sha256": EXPECTED_CENSUS,
            "boundary": "Static source classification only; kernel identity, joint feasibility and semantic-owner confirmation remain separate",
            "counts": {"source_candidates": len(result), "role_reviewed": len(reviewed),
                       "role_pending": len(result)-len(reviewed), "semantic_owners_unresolved": len(result),
                       "new_joint_witnesses": 0}, "declarations": result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    output = args.out.resolve()
    if output.is_relative_to(REPO):
        parser.error("H44: output must be outside repository")
    source = authenticated_census(args.census)
    curated_bytes = CURATED.read_bytes()
    curated = json.loads(curated_bytes)
    if curated["source_census_sha256"] != EXPECTED_CENSUS or curated["base"] != source["base"]:
        raise ValueError("curation census/base provenance differs")
    result = classify(source, curated)
    result["curation_sha256"] = hashlib.sha256(curated_bytes).hexdigest()
    output.mkdir(parents=True, exist_ok=False)
    data = (json.dumps(result, indent=2, ensure_ascii=False) + "\n").encode()
    (output / "classification.json").write_bytes(data)
    (output / "SHA256SUMS").write_text(hashlib.sha256(data).hexdigest()+"  classification.json\n")
    print(json.dumps(result["counts"], sort_keys=True))
    if args.require_complete and (result["counts"]["role_pending"] or result["counts"]["semantic_owners_unresolved"]):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
