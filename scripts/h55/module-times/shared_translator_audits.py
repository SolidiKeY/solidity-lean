#!/usr/bin/env python3
"""Guard regression: shared translator audits are mistaken for source adequacy or current runtime acceptance."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "tests/directruntime-20261104/shared-translator/"
DOC = "docs/feature-work/directruntime-shared-translator.md"
ROLES = {
    PREFIX + "ApiSignatures.lean": ("shared reader and obligation API signature checks", DOC),
    PREFIX + "AxiomInventory.lean": ("shared executable boundary and scope theorem axiom inspection", DOC),
    PREFIX + "H90Census.lean": ("fixture-driven canonical-reader printed-body and name parity census", DOC),
}


def classify(root, index):
    root = Path(root).resolve()
    if not isinstance(index, dict) or not isinstance(index.get("rows"), list):
        raise ValueError("invalid index")
    rows, seen = [], set()
    for item in index["rows"]:
        row = item["candidate"]
        path = row["path"]
        if path not in ROLES or item["status"] != "no-supplied-current-reference":
            continue
        if path in seen:
            raise ValueError("unreviewed or duplicate fixture")
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError("invalid fixture path")
        if hashlib.sha256(source.read_bytes()).hexdigest() != row["sha256"]:
            raise ValueError("fixture differs from index")
        seen.add(path)
        rows.append({"candidate": row, "role": ROLES[path][0], "source_document": ROLES[path][1], "source_document_sha256": hashlib.sha256((root / ROLES[path][1]).read_bytes()).hexdigest(),
            "driver": "handoff describes per-file inspections and a fixture census; exact current invocation and result unverified",
            "inputs": "Lean imports; H90Census reads absent artifacts/h90/cr-census-inputs.json and listed fixture paths; workspace and toolchain unresolved",
            "effects": "Lean checks and axiom diagnostics; H90Census writes artifacts/h90/cr-census-results.json; other driver effects unresolved",
            "expected_outcome": "current exit and output unverified; census and inspections do not establish Source adequacy, semantic closure or module timing",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: shared_translator_audits.py INDEX.json", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
            "coverage": "supplied-snapshot-subset-only-unverified",
            "limitations": "auxiliary inputs and handoff changes are not tracked by candidate drift; recheck before reuse",
            "census_input_present": (ROOT / PREFIX / "artifacts/h90/cr-census-inputs.json").is_file(),
            "input_sha256": hashlib.sha256(raw).hexdigest(),
            "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f"shared translator audit classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
