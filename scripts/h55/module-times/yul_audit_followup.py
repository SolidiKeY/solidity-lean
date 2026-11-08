#!/usr/bin/env python3
"""Guard regression: Yul allocation witnesses and reservation-policy refutations are conflated with runtime adequacy."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "tests/h62/item2/audit-yul/"
DOC = "docs/feature-work/h62-2-audit-yul.md"
ROLES = {
    "AllocationWitnesses": "ordinary allocation joint witnesses and separate H69 separation certificates",
    "ReservedRefutation": "H69 refutation of SLOTNUM reservation membership; not a success contract or new exclusion",
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
            "driver": "audit source and handoff record witness and refutation roles; exact current driver and invocation unresolved",
            "inputs": "Lean toolchain and imports; actual current workspace, cache and dependency products unresolved",
            "effects": "Lean diagnostics and axiom text; output artifact paths and side effects depend on unresolved driver",
            "expected_outcome": "current exit and output unverified; no runtime memory, executable builtin, fork or gas adequacy established",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: yul_audit_followup.py INDEX.json", file=sys.stderr)
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
        print(f"Yul audit follow-up classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
