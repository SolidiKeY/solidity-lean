#!/usr/bin/env python3
"""Exhaustive candidate/fixture accounting; no semantic success is inferred."""
import argparse
import difflib
import json
from pathlib import Path
import subprocess
import candidate_inventory as census
import bulk_inputs
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


def account(catalog, manifest, sources):
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
    result = account(catalog, manifest, sources)
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
