#!/usr/bin/env python3
"""Explicit embedded Checks regions, first tranche. External source audit only."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from census import ROOT, mask
from classify import BASE, FACETS, INVENTORY_SHA256

FACETS = dict(FACETS, boundneg="Required array read bound fails for the wrong reference; not allocation/admission refusal", heap_keeps="Actual Heap.Keeps of old object contents, not just lengths", lengths="Old array lengths preserved; no Heap.Keeps claim", continuation="Continuation relates original depth+steps source execution to reexported residual execution for every depth, retaining every error class")

MAP = ROOT / "tests/h62/item4/generic-internalflow/embedded-cases.txt"
REGIONS = {
    "RuntimeFrameV3AllocatingSource.lean": (130, 244),
    "RuntimeFrameV3MutatingSource.lean": (180, 324),
    "RuntimeFrameV3AllocatingResume.lean": (216, 317),
    "RuntimeFrameV3MutatingResume.lean": (210, 381),
}

def parse(text, regions=None, facet_definitions=None):
    regions = REGIONS if regions is None else regions
    definitions = FACETS if facet_definitions is None else facet_definitions
    mapping = {}
    current = None
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("@"):
            current = "RuntimeFrame" + line[1:] + ".lean"
            if current in mapping:
                raise ValueError("duplicate region")
            mapping[current] = {}
            continue
        if current is None:
            raise ValueError("case outside region")
        facets, names = line.split(":", 1)
        tags = facets.split(",")
        if set(tags) - definitions.keys() or len(set(tags)) != len(tags) or not names.split():
            raise ValueError("unknown/duplicate facet or empty group")
        for name in names.split():
            if name in mapping[current]:
                raise ValueError("duplicate case")
            mapping[current][name] = tags
    if set(mapping) != set(regions):
        raise ValueError("region inventory mismatch")
    return mapping

def classify(inventory, mapping, regions=None, facet_definitions=None):
    regions = REGIONS if regions is None else regions
    definitions = FACETS if facet_definitions is None else facet_definitions
    result = []
    count = fixtures = 0
    for file in inventory["files"]:
        name = Path(file["path"]).name
        if name not in regions:
            continue
        begin, end = regions[name]
        original = subprocess.check_output(["git", "show", BASE+":"+file["path"]], cwd=ROOT)
        if hashlib.sha256(original).hexdigest() != file["source_sha256"]:
            raise ValueError("source hash mismatch")
        if (ROOT / file["path"]).read_bytes() != original:
            raise ValueError("original source changed")
        lines = mask(original.decode()).splitlines()
        if lines[begin-1].strip() != "namespace Checks" or lines[end-1].strip() != "end Checks":
            raise ValueError("namespace boundary mismatch")
        # These four simple regions have no nested namespace/section/mutual commands.
        if any(re.match(r"\s*(namespace|section|mutual|end)\b", line) for line in lines[begin:end-1]):
            raise ValueError("nested region requires explicit adjudication")
        selected = [d for d in file["declarations"] if begin < d["line"] < end]
        cases = [d for d in selected if d["kind"] == "theorem"]
        if len({d["name"] for d in cases}) != len(cases) or set(mapping[name]) != {d["name"] for d in cases}:
            raise ValueError("missing/extra/ambiguous cases")
        rows = []
        for d in selected:
            row = dict(d)
            row["facets"] = mapping[name][d["name"]] if d["kind"] == "theorem" else []
            row["role"] = "semantic_case" if d["kind"] == "theorem" else "fixture"
            row["audit9"] = "Supports allocating/mutating body-effects distinction. Preserve old Heap.Keeps only where stated; mutating prefixes preserve lengths, not old contents. No substitution or migration approved."
            row["audit11"] = "No confirmed named duplicate helper here; typed halt-constructor separation is a candidate only after exact semantic run witnesses."
            row["audit16"] = "Retain complete typed fixture/header and every quantified/conjoined obligation; observations may be table data, execution proofs must remain semantic kernel proofs. No H55 overlap."
            rows.append(row)
        result.append({"path": file["path"], "source_sha256": file["source_sha256"], "namespace": "Checks", "begin": begin, "end": end, "declarations": rows})
        count += len(cases)
        fixtures += len(selected)-len(cases)
    if len(result) != len(regions):
        raise ValueError("missing original region")
    return {"schema": 1, "base": BASE, "scope": "Only four explicitly bounded embedded Checks regions. Other embedded controls remain pending; no full checkpoint completion.", "boundary": "Source classification, not elaboration or semantic proof. Facets summarize; exact headers retain all premises/conjuncts. Counts are declarations, not executions.", "facet_definitions": definitions, "files": result, "summary": {"regions": len(result), "theorems": count, "fixtures": fixtures, "unclassified_within_selected_regions": 0}}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inventory", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    a = ap.parse_args()
    data = a.inventory.read_bytes()
    if hashlib.sha256(data).hexdigest() != INVENTORY_SHA256:
        raise SystemExit("frozen inventory mismatch")
    output = a.output.resolve()
    if output.is_relative_to(ROOT.resolve()) or output == a.inventory.resolve() or (output.exists() and output.samefile(a.inventory)):
        raise SystemExit("output must be off git and distinct from frozen inventory")
    result = classify(json.loads(data), parse(MAP.read_text()))
    encoded = json.dumps(result, sort_keys=True, ensure_ascii=False, indent=2)+"\n"
    output.write_text(encoded)
    print(json.dumps({**result["summary"], "sha256": hashlib.sha256(encoded.encode()).hexdigest()}))

if __name__ == "__main__":
    main()
