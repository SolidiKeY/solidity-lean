#!/usr/bin/env python3
"""Guard regression: standalone decision witnesses are mistaken for complete decision coverage or runtime timing."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
DOC = "docs/feature-work/after-roadmap-va1.md"
PREFIX = "docs/feature-work/after-roadmap-va1/"
ROLES = {
    PREFIX + "coefficient-boundary-link.lean": ("retained source coefficient witness linked to generic boundary", DOC),
    PREFIX + "coverage-counterexample.lean": ("standalone kernel witness distinguishing source target and coverage predicates", DOC),
    PREFIX + "two-prefix-normalization-client.lean": ("two-quantifier normalization client and adjacent fuel controls", DOC),
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
            "driver": "handoff describes standalone Lean controls; exact current invocation and result remain unverified",
            "inputs": "Lean imports and in-source formulas; actual workspace, dependencies and toolchain identity unresolved",
            "effects": "Lean evaluation, checks and printed axiom diagnostics; external driver effects unresolved",
            "expected_outcome": "current exit and output unverified; these witnesses do not establish complete decision coverage or module timing",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: va1_standalone_controls.py INDEX.json", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
            "coverage": "supplied-snapshot-subset-only-unverified",
            "input_sha256": hashlib.sha256(raw).hexdigest(),
            "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f"VA1 standalone classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
