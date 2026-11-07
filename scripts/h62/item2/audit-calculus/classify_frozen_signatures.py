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
from bulk_inputs import bulk_bytes

EXPECTED_CENSUS = "a2aa6d5e5837eac11ad80fc4eb59e4c3903e9d7f9d52e41bcbccb1e24dccc2da"
REPO = Path(__file__).resolve().parents[4]


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
    files = curated.get("reviewed_files", [curated.get("reviewed_file")])
    known_files = {row["file"] for row in declarations}
    if not isinstance(files, list) or not files or any(not isinstance(file, str) for file in files):
        raise ValueError("invalid reviewed file roster")
    if len(set(files)) != len(files) or not set(files) <= known_files:
        raise ValueError("duplicate or unknown reviewed file")
    expected = {row["id"] for row in declarations if row["file"] in files}
    if set(reviewed) != expected:
        raise ValueError("reviewed file has unaccounted declarations")
    owners = curated.get("semantic_owner_by_file", {})
    source_hashes = {row["path"]: row["sha256"] for row in source.get("sources", [])}
    if not isinstance(owners, dict):
        raise ValueError("invalid semantic-owner map")
    for file, owner in owners.items():
        if file not in known_files or not isinstance(owner, dict):
            raise ValueError("unknown semantic-owner file")
        if owner.get("source_sha256") != source_hashes.get(file) or file not in source_hashes:
            raise ValueError("semantic-owner source hash differs")
        if (owner.get("status") != "confirmed"
                or owner.get("authority_kind") != "coordinator-user-answer"
                or not isinstance(owner.get("owner"), str) or not owner["owner"].strip()
                or not isinstance(owner.get("authority"), str) or not owner["authority"].strip()):
            raise ValueError("semantic owner lacks explicit authoritative confirmation")
    result = []
    for original in declarations:
        row = {key: original[key] for key in ["id", "file", "line", "source_name", "signature_sha256"]}
        if original["file"] in owners:
            row["semantic_owner"] = dict(owners[original["file"]])
            row["semantic_owner_status"] = "confirmed: " + owners[original["file"]]["owner"]
        else:
            row["semantic_owner"] = {"status": "unresolved"}
            row["semantic_owner_status"] = "unresolved; migration scope does not establish live semantic ownership"
        if original["id"] in reviewed:
            row.update(role_status="reviewed static source classification", roles=reviewed[original["id"]])
        else:
            row["role_status"] = "pending semantic review; no premise/conclusion role inferred"
        result.append(row)
    return {"schema_version": 1, "base": source["base"], "source_census_sha256": EXPECTED_CENSUS,
            "boundary": "Static source classification only; kernel identity, joint feasibility and semantic-owner confirmation remain separate",
            "counts": {"source_candidates": len(result), "role_reviewed": len(reviewed),
                       "role_pending": len(result)-len(reviewed), "semantic_owners_unresolved": sum(row["semantic_owner"]["status"] != "confirmed" for row in result),
                       "new_joint_witnesses": 0}, "declarations": result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", type=Path, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--out", type=Path, help="write the full external report")
    mode.add_argument("--check-only", action="store_true",
                      help="validate all inputs and acceptance without writing a report")
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    output = args.out.resolve() if args.out is not None else None
    if output is not None and output.is_relative_to(REPO):
        parser.error("H44: output must be outside repository")
    source = authenticated_census(args.census)
    curated_bytes = bulk_bytes("lifetime_roles")
    curated = json.loads(curated_bytes)
    if curated["source_census_sha256"] != EXPECTED_CENSUS or curated["base"] != source["base"]:
        raise ValueError("curation census/base provenance differs")
    result = classify(source, curated)
    result["curation_sha256"] = hashlib.sha256(curated_bytes).hexdigest()
    if output is not None:
        output.mkdir(parents=True, exist_ok=False)
        data = (json.dumps(result, indent=2, ensure_ascii=False) + "\n").encode()
        (output / "classification.json").write_bytes(data)
        (output / "SHA256SUMS").write_text(hashlib.sha256(data).hexdigest()+"  classification.json\n")
    print(json.dumps(result["counts"], sort_keys=True))
    if args.require_complete and (result["counts"]["role_pending"] or result["counts"]["semantic_owners_unresolved"]):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
