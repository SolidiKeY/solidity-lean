#!/usr/bin/env python3
"""Guard regression: adapter audit witnesses are counted as compiler or execution adequacy."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "tests/h62/item2/audit-v08-adapters/"
DOC = "docs/feature-work/h62-2-audit-v08-adapters.md"
ROLES = {
    "FailureResourceWitnesses": "joint-premise failure-resource interface witnesses",
    "LocalGuardStatementCensus": "kernel-environment census of local guard definitions and types",
    "LocalGuardSuccess": "dynamic local guard success, failure and compiler-refutation controls",
    "P8StatementCensus": "kernel-environment census of P8 and V08 interfaces with optional world census",
    "ResourceStatementCensus": "kernel-environment census of failure resource definitions and types",
    "RuntimeFrameStatementCensus": "kernel-environment census of runtime-frame interface definitions and types",
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
            "driver": "audit source and handoff are static references; exact current driver and invocation unresolved",
            "inputs": "Lean toolchain and imports; P8 optional H62_WORLD_CENSUS environment flag; current workspace, cache and dependencies unresolved",
            "effects": "Lean diagnostics and axiom text; output artifact paths and side effects depend on unresolved driver",
            "expected_outcome": "current exit and output unverified; no compiler, execution or gas/fork adequacy acceptance claimed",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: v08_audit_controls.py INDEX.json", file=sys.stderr)
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
        print(f"v08 audit classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
