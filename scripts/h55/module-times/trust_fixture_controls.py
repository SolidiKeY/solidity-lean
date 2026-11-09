#!/usr/bin/env python3
"""Guard regression: trust audit fixtures are counted as a project-wide axiom audit."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "tests/h62/item1/trust-fragments/"
DOC = "docs/feature-work/h62-1-trust-fragments.md"
ROLES = {
    "Fixture": "isolated propext-dependent theorem and allowed-axiom audit loop",
    "FixtureAddon": "isolated imported addon witness for fixture harness controls",
}


def classify(root, index):
    root = Path(root).resolve()
    if not isinstance(index, dict) or not isinstance(index.get("rows"), list):
        raise ValueError("invalid index")
    rows, seen = [], set()
    for item in index["rows"]:
        row = item["candidate"]
        path = row["path"]
        if not path.startswith(PREFIX) or item["status"] != "no-supplied-current-reference":
            continue
        name = path[len(PREFIX):]
        if not name.endswith(".lean") or name[:-5] not in ROLES:
            continue
        if path in seen:
            raise ValueError("unreviewed or duplicate fixture")
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError("invalid fixture path")
        if hashlib.sha256(source.read_bytes()).hexdigest() != row["sha256"]:
            raise ValueError("fixture differs from index")
        seen.add(path)
        rows.append({"candidate": row, "role": ROLES[name[:-5]],
            "driver": "check_fixture.py describes isolated positive and negative audit controls; exact current invocation unresolved",
            "inputs": "Lean toolchain and imports; actual current workspace, cache and dependency products unresolved",
            "effects": "historical harness copies fixture files and writes isolated oleans and logs; current paths and effects unresolved",
            "expected_outcome": "current exit and output unverified; fixture audit is not a project-wide axiom audit",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: trust_fixture_controls.py INDEX.json", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        doc = ROOT / DOC
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
            "coverage": "supplied-snapshot-subset-only-unverified",
            "input_sha256": hashlib.sha256(raw).hexdigest(),
            "source_document": DOC,
            "source_document_sha256": hashlib.sha256(doc.read_bytes()).hexdigest(),
            "driver_source": "scripts/h62/item1/trust-fragments/check_fixture.py",
            "driver_sha256": hashlib.sha256((ROOT / "scripts/h62/item1/trust-fragments/check_fixture.py").read_bytes()).hexdigest(),
            "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f"trust fixture classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
