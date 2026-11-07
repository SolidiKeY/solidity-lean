#!/usr/bin/env python3
"""Normalize elaborated inspection output and attach explicit snapshot owners.

Does not infer theorem coverage, premises, or owner permission. Missing owners,
generated theorem origins, uninspected modules and parent obligations stay open.
"""
import argparse
import fnmatch
import hashlib
import json
from pathlib import Path
import subprocess
import re
from collections import Counter
from elaborated_census import TEMPLATE, manifest_sha256
from census import BASE, declarations, mapped_paths


OWNERSHIP_SHA256 = '49fa4e0ef45307428a026b414efc6a99efcbf4911dd23e9574e806be54dbfefe'


def validate_pins(pins, mapped):
    if pins["inspection_template_sha256"] != hashlib.sha256(TEMPLATE.encode()).hexdigest():
        raise ValueError("inspection template mismatch")
    paths = set(pins["source_sha256"])
    modules = pins["modules"]
    if pins["base"] != BASE or not paths <= set(mapped):
        raise ValueError("wrong base or unmapped source")
    if len(set(modules)) != len(modules) or set(modules) != {path[:-5].replace("/", ".") for path in paths}:
        raise ValueError("module/source manifest mismatch")
    if pins["manifest_sha256"] != manifest_sha256(pins):
        raise ValueError("manifest fingerprint mismatch")


def read_records(text, pins):
    rows, completed = [], []
    for line in text.splitlines():
        if line.startswith("H62_CENSUS_JSON "):
            rows.append(json.loads(line[len("H62_CENSUS_JSON "):]))
        elif line.startswith("H62_CENSUS_DONE "):
            completed.append(json.loads(line[len("H62_CENSUS_DONE "):]))
        elif re.search(r"(?:^|:\d+:\d+: )(?:error|warning)(?:\([^)]*\))?:", line):
            raise ValueError("inspection diagnostic")
    if len(completed) != 1:
        raise ValueError("missing unique completion marker")
    expected = pins["manifest_sha256"]
    if completed[0]["manifest_sha256"] != expected or any(row["manifest_sha256"] != expected for row in rows):
        raise ValueError("inspection manifest mismatch")
    counts = Counter(row["module"] for row in rows)
    if completed[0]["counts"] != {module: counts[module] for module in pins["modules"]} or set(counts) - set(pins["modules"]):
        raise ValueError("per-module completion mismatch")
    if len({row["name"] for row in rows}) != len(rows):
        raise ValueError("duplicate declaration")
    return rows


def owner_matches(path, items):
    matches = []
    for item in items:
        exclusions = [pattern.strip() for pattern in item.get("writeExclusions", "").split(";") if pattern.strip()]
        if any(fnmatch.fnmatchcase(path, pattern) for pattern in exclusions):
            continue
        for pattern in item.get("writeScope", "").split(";"):
            pattern = pattern.strip()
            if pattern and fnmatch.fnmatchcase(path, pattern):
                matches.append({"id": item["id"], "owner": item["owner"], "scope": pattern})
    return matches


def source_links(rows, candidates):
    """Require unique name+selection-position matches; preserve both gap directions."""
    keys = [(c["name_candidate"], c["name_line"], c["name_column"]) for c in candidates]
    if len(set(keys)) != len(keys):
        raise ValueError("duplicate source candidate location")
    for row in rows:
        if row["kind"] == "theorem":
            row["source_origin"] = "generated_or_private_unresolved"
            row["source_match_count"] = 0
            row.pop("source_signature_sha256", None)
    result = []
    for candidate in candidates:
        matches = []
        for row in rows:
            position = row.get("declaration_range") or {}
            if (row["kind"] == "theorem" and row.get("is_theorem")
                    and row.get("user_name") == candidate["name_candidate"]
                    and position.get("selection_line") == candidate["name_line"]
                    and position.get("selection_column") == candidate["name_column"]):
                matches.append(row)
        status = "unique" if len(matches) == 1 else "ambiguous" if matches else "unmatched"
        result.append(dict(candidate, kernel_names=sorted(row["name"] for row in matches), match_count=len(matches), mapping_status=status, mapping_method="module + normalized user name + original theorem + Unicode selection position"))
        for row in matches:
            row["source_origin"] = ("private_source_theorem" if row.get("private") else "named_source_theorem") if status == "unique" else "ambiguous_source_match"
            row["source_signature_sha256"] = candidate["signature_sha256"]
            row["source_match_count"] = len(matches)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, required=True)
    p.add_argument("--log", type=Path, required=True)
    p.add_argument("--pins", type=Path, required=True)
    p.add_argument("--inspection", type=Path, required=True)
    p.add_argument("--ownership", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    repo = args.repo.resolve()
    all_paths, _ = mapped_paths(repo)
    pins = json.loads(args.pins.read_text())
    validate_pins(pins, all_paths)
    if hashlib.sha256(args.inspection.read_bytes()).hexdigest() != pins["inspection_sha256"]:
        raise ValueError("inspection source checksum mismatch")
    source = {}
    for path, expected in pins["source_sha256"].items():
        data = (repo / path).read_bytes()
        if hashlib.sha256(data).hexdigest() != expected or data != subprocess.check_output(["git", "show", BASE + ":" + path], cwd=repo):
            raise ValueError("changed frozen source: " + path)
        module = path[:-5].replace("/", ".")
        source[module] = declarations(data.decode())
    snapshot_data = args.ownership.read_bytes()
    if hashlib.sha256(snapshot_data).hexdigest() != OWNERSHIP_SHA256:
        raise ValueError("ownership snapshot checksum mismatch")
    snapshot = json.loads(snapshot_data)
    scope_items = [v for v in snapshot["items"] if v.get("id", "").startswith("H30-WRITER")]
    rows = []
    for row in read_records(args.log.read_text(), pins):
        path = row["module"].replace(".", "/") + ".lean"
        matches = owner_matches(path, scope_items)
        owners = sorted({item["owner"] for item in matches})
        row["owner"] = owners[0] if len(owners) == 1 else None
        row["owner_evidence"] = sorted(matches, key=lambda item: (item["id"], item["scope"]))
        row["owner_status"] = "explicit_snapshot_match" if len(owners) == 1 else "conflict" if owners else "unresolved"
        row["source_path"] = path
        row["type_expr_sha256"] = hashlib.sha256(row["type_expr"].encode()).hexdigest()
        row["body_expr_sha256"] = hashlib.sha256(row["body_expr"].encode()).hexdigest() if row.get("body_expr") is not None else None
        row["role"] = "proof_statement" if row["kind"] == "theorem" else "proof_valued_constant" if row["proof_type"] else "proposition_valued_constant" if row.get("predicate_valued") else "data_constant"
        if row["kind"] == "theorem":
            row["source_origin"] = "generated_or_private_unresolved"
        row["witness"] = None
        row["coverage"] = "uncovered; linkage review required"
        rows.append(row)
    rows.sort(key=lambda row: (row["module"], row["name"]))
    if len({row["name"] for row in rows}) != len(rows):
        raise ValueError("empty or duplicate inventory")
    source_mapping = {module: source_links([row for row in rows if row["module"] == module], candidates) for module, candidates in sorted(source.items())}
    missing = sorted(set(all_paths) - pins["source_sha256"].keys())
    result = {"base": BASE, "boundary": "Elaborated direct fields and constants for selected core modules only; not flattened parent obligations or full-area coverage", "ownership_snapshot_sha256": hashlib.sha256(snapshot_data).hexdigest(), "inspected_modules": pins["modules"], "uninspected_paths": missing, "source_mapping": source_mapping, "records": rows, "summary": {"records": len(rows), "proposition_valued_constants": sum(r.get("predicate_valued", False) for r in rows), "source_candidates": sum(len(v) for v in source_mapping.values()), "source_candidates_unique": sum(r["mapping_status"] == "unique" for values in source_mapping.values() for r in values), "source_candidates_unmatched": sum(r["mapping_status"] == "unmatched" for values in source_mapping.values() for r in values), "source_candidates_ambiguous": sum(r["mapping_status"] == "ambiguous" for values in source_mapping.values() for r in values), "direct_fields": sum(r["kind"] == "field" for r in rows), "proof_fields": sum(r["kind"] == "field" and r["proof_type"] for r in rows), "uninspected_files": len(missing), "unresolved_owner_records": sum(r["owner"] is None for r in rows), "mechanically_linked_witnesses": 0}}
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(result["summary"], sort_keys=True))


if __name__ == "__main__":
    main()
