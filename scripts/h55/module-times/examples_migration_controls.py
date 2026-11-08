#!/usr/bin/env python3
"""Guard regression: examples migration API fixtures are counted as Solidity program or interface-equivalence proofs."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "tests/h62/item6/migrate-examples/"
DOC = "docs/feature-work/h62-6-migrate-examples.md"
ROLES = {
    "ApiFixture": "isolated parser, elaborator, evaluator and generated-theorem API fixture",
    "InterfaceDump": "audit-only serializer of loaded Examples constants and normalized type expressions",
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
            "driver": "migration handoff records historical probes; full InterfaceDump awaits successful all-module compilation; exact current invocation unresolved",
            "inputs": "Lean toolchain and imports; actual current workspace, cache and dependency products unresolved",
            "effects": "InterfaceDump opens H62_INTERFACE_OUTPUT for writing; other effects depend on unresolved driver",
            "expected_outcome": "current exit and output unverified; no Solidity program property or interface equivalence established",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: examples_migration_controls.py INDEX.json", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        doc = ROOT / DOC
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
            "coverage": "supplied-snapshot-subset-only-unverified",
            "input_sha256": hashlib.sha256(raw).hexdigest(),
            "source_document": DOC,
            "source_document_sha256": hashlib.sha256(doc.read_bytes()).hexdigest(),
            "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f"Examples migration classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
