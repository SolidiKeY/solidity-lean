#!/usr/bin/env python3
"""Exhaustive candidate/fixture accounting; no semantic success is inferred."""
import argparse
import collections
import difflib
import json
from pathlib import Path
import subprocess
import candidate_inventory as census
import bulk_inputs
from engine import KINDS, SCORED
from archive_io import require


def changed_spans(original, replacement, offset=0):
    """Character offsets in the original, retaining zero-width insertions."""
    return [{"start": offset + i, "stop": offset + j, "kind": tag}
            for tag, i, j, _, _ in difflib.SequenceMatcher(None, original, replacement, autojunk=False).get_opcodes()
            if tag != "equal"]


def overlaps(edit, span):
    if edit["start"] == edit["stop"]:
        return span["start"] <= edit["start"] < span["stop"]
    return edit["start"] < span["stop"] and span["start"] < edit["stop"]


def case_counts(cases):
    scored = [c for c in cases if c["kind"] in SCORED]
    return {"case_ids": len(cases), "scored_ids": len(scored),
            "distinct_scored_programs": len({c["mutant_sha256"] for c in scored}),
            "unscored_runner_controls": len(cases) - len(scored),
            "distinct_programs_all_roles": len({c["mutant_sha256"] for c in cases}),
            "roles": dict(collections.Counter(c["kind"] for c in cases))}


def validate_case_hashes(cases):
    by_hash = {}
    by_id = {c["id"]: c for c in cases}
    require(len(by_id) == len(cases), "duplicate selected ID")
    for case in cases:
        require(case["kind"] in KINDS, "unknown case role")
        by_hash.setdefault(case["mutant_sha256"], []).append(case)
    survivors = [c for c in cases if c["kind"] == "runner-survivor-control"]
    require(len(survivors) <= 1, "multiple survivor controls")
    for control in survivors:
        parent = by_id.get(control.get("control_of"))
        require(parent is not None and parent["kind"] in SCORED
                and control["mutant_sha256"] == parent["mutant_sha256"]
                and bool(control.get("regression")), "undeclared duplicate mutant hash or unlinked survivor control")
    for group in by_hash.values():
        if len(group) == 1:
            continue
        scored = [c for c in group if c["kind"] in SCORED]
        controls = [c for c in group if c["kind"] == "runner-survivor-control"]
        require(len(group) == 2 and len(scored) == len(controls) == 1
                and controls[0].get("control_of") == scored[0]["id"]
                and "regression" in controls[0], "undeclared duplicate mutant hash")


def validate_catalog(catalog, sources, inventory, manifest):
    require(set(census.INPUTS[:2]) <= set(sources), "missing candidate source file")
    require(catalog["production_inputs"] == {f: census.digest(s.encode()) for f, s in sources.items()}, "catalog/source input identity mismatch")
    expected = []
    for file in census.INPUTS[:2]:
        for row in census.declarations(sources[file], file):
            row["clauses"] = census.premise_clauses(sources[file], row)
            expected.append(row)
    keys = ("id", "kind", "file", "span", "clauses")
    require([{k: row[k] for k in keys} for row in catalog["declarations"]] == expected,
            "catalog differs from exhaustive source declarations or units")
    selected = {c["constructor_id"] for c in manifest["cases"]}
    index = inventory["inventory"]
    require(len(index) == len({row["id"] for row in index}) and {row["id"] for row in index} == selected,
            "selected inventory declaration set mismatch")
    expected_by_id = {row["id"]: row for row in expected}
    require(inventory["base"] == manifest["base"] == census.BASE, "selected inventory base mismatch")
    require(inventory["production_inputs"] == manifest["production_inputs"], "selected inventory/manifest input mismatch")
    require(all(file in sources and census.digest(sources[file].encode()) == sha for file, sha in inventory["production_inputs"].items()), "selected inventory input identity mismatch")
    for row in index:
        require(row["id"] in expected_by_id, "selected inventory declaration missing from source")
        original = expected_by_id[row["id"]]; span = original["span"]
        require((row["file"], row["line_start"], row["line_end"], row["span_sha256"]) ==
                (original["file"], span["line_start"], span["line_end"], span["sha256"]),
                "selected inventory/source span mismatch")


def account(catalog, manifest, sources, inventory):
    validate_case_hashes(manifest["cases"])
    require("declared_case_counts" in manifest, "declared case counts are required")
    require(manifest["declared_case_counts"] == case_counts(manifest["cases"]), "declared case/program counts mismatch")
    validate_catalog(catalog, sources, inventory, manifest)
    declarations = catalog["declarations"]
    by_id = {r["id"]: r for r in declarations}
    require(len(by_id) == len(declarations), "duplicate candidate declaration")
    cases = manifest["cases"]
    require(len({c["id"] for c in cases}) == len(cases), "duplicate selected ID")
    edits = {}
    for c in cases:
        require(c["constructor_id"] in by_id, "missing selected declaration")
        row = by_id[c["constructor_id"]]; text = sources[c["target"]]
        require(row["file"] == c["target"] and text.count(c["old"]) == 1, "source attribution mismatch")
        start = text.index(c["old"]); end = start + len(c["old"])
        require(row["span"]["start"] <= start < end <= row["span"]["stop"], "edit outside candidate span")
        require(census.digest(text.encode()) == c["target_sha256"], "target hash mismatch")
        require(census.digest(text.replace(c["old"], c["new"], 1).encode()) == c["mutant_sha256"], "mutant hash mismatch")
        edits[c["id"]] = changed_spans(c["old"], c["new"], start)
        require(edits[c["id"]], "unchanged selected variant")
    rows = []; unit_ids = set()
    for row in declarations:
        selected = [c["id"] for c in cases if c["constructor_id"] == row["id"]]
        units = []
        for index, clause in enumerate(row["clauses"]):
            ident = row["id"] + "/unit-" + str(index)
            require(ident not in unit_ids, "duplicate source unit"); unit_ids.add(ident)
            touching = [ident for ident in selected if any(overlaps(edit, clause) for edit in edits[ident])]
            units.append({"id": ident, "source": clause, "touching_case_ids": touching,
                          "disposition": "selected-textual-edit" if touching else "unselected-textual-unit"})
        rows.append({"id": row["id"], "kind": row["kind"], "file": row["file"], "span": row["span"],
                     "selected_case_ids": selected, "units": units,
                     "disposition": "selected-variant-source" if selected else "unselected-candidate",
                     "claim": "No universal declaration soundness or equivalence inferred."})
    fixtures = []
    for fixture in catalog["fixtures"]:
        roles = [{"case_id": c["id"], "role": role} for c in cases
                 for role in ("oracle", "witness", "equivalence", "regression") if c.get(role) == fixture["file"]]
        fixtures.append({**fixture, "selected_roles": roles,
                         "disposition": "selected-oracle-input" if roles else "unselected-fixture"})
    fixture_paths = {f["file"] for f in fixtures}
    require(all(c[role] in fixture_paths for c in cases for role in ("oracle", "witness", "equivalence", "regression") if role in c), "unaccounted selected fixture")
    return {"declarations": rows, "fixtures": fixtures, "profiles": catalog["frozen_manifests"],
            "cases": [{"id": c["id"], "kind": c["kind"], "family": c.get("family"),
                       "declaration": c["constructor_id"], "mutant_sha256": c["mutant_sha256"],
                       "changed_spans": edits[c["id"]],
                       "outside_textual_units": [e for e in edits[c["id"]] if not any(overlaps(e, unit) for unit in by_id[c["constructor_id"]]["clauses"])],
                       "execution_status": "requires-whole-run-receipt"} for c in cases],
            "counts": {"declarations": len(rows), "units": len(unit_ids), "fixtures": len(fixtures),
                       "profiles": len(catalog["frozen_manifests"]), "selected_ids": len(cases)},
            "program_counts": case_counts(cases),
            "scope_complete": False, "score": None,
            "boundary": "Exhaustive source and selection accounting only. Unselected is not excluded, equivalent, killed or proved sound. Semantic acceptance requires actual proof/run receipts."}


def build(repo, manifest_path):
    require(not subprocess.check_output(["git", "status", "--porcelain"], cwd=repo), "commit inputs before ledger generation")
    manifest_bytes = bulk_inputs.read(repo, manifest_path)
    manifest = json.loads(manifest_bytes); catalog = census.build(repo)
    composed = {}
    for pin in manifest["composition_sources"]:
        data = bulk_inputs.read(repo, repo / pin["file"])
        require(census.digest(data) == pin["sha256"], "composition source hash mismatch")
        for case in json.loads(data)["cases"]:
            require(case["id"] not in composed or composed[case["id"]] == case, "composition changes a reused case")
            composed[case["id"]] = case
    require(manifest["cases"] == list(composed.values()), "selected suite differs from exact composition")
    sources = {file: subprocess.check_output(["git", "show", census.BASE + ":" + file], cwd=repo).decode()
               for file in catalog["production_inputs"]}
    require(all(census.digest(sources[p].encode()) == h for p, h in catalog["production_inputs"].items()), "census source drift")
    inventory_bytes = bulk_inputs.read(repo, repo / manifest["inventory"])
    require(census.digest(inventory_bytes) == manifest["inventory_sha256"], "selected inventory file hash mismatch")
    result = account(catalog, manifest, sources, json.loads(inventory_bytes))
    result.update(schema=1, base=census.BASE,
                  input_head=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip(),
                  manifest=str(manifest_path.relative_to(repo)), manifest_sha256=census.digest(manifest_bytes),
                  production_inputs=catalog["production_inputs"])
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(); parser.add_argument("manifest", type=Path); parser.add_argument("output", type=Path); args = parser.parse_args()
    repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    require(not args.output.resolve().is_relative_to(repo), "generated ledger belongs off Git")
    ledger = build(repo, args.manifest.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x") as stream:
        json.dump(ledger, stream, indent=2); stream.write("\n")
    print(json.dumps({"output": str(args.output.resolve()), "sha256": census.digest(args.output.read_bytes()), **ledger["counts"], "scope_complete": False}, indent=2))
