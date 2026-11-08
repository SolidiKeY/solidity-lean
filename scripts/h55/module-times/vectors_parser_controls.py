#!/usr/bin/env python3
"""Guard regression: Lean syntax probes are mistaken for elaboration, proof validation or authenticated module timing."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "scripts/h55/vectors-tables/"
DOC = "scripts/h55/vectors-tables/raw_context.py"
ROLES = {
    "ParseContext": "Lean syntax probe emitting declaration boundaries and selected parser-node spans",
    "ParseProbe": "Lean syntax probe emitting selected parser-node kinds and spans",
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
            "driver": "raw_context.py invokes ParseContext; run_raw_parser.py and raw_master_reconcile.py invoke ParseProbe; current invocation remains unverified",
            "inputs": "path arguments, imported Lean parser, hard-coded Lean 4.24 sysroot; current workspace and toolchain identity unverified",
            "effects": "stdout contains FILE/NODE/END markers and ParseContext declaration markers; driver modes may write external logs or JSON, or the in-repository context manifest if absent",
            "expected_outcome": "current exit and output unverified; syntax-only observations do not establish elaboration, proofs or module timing",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: vectors_parser_controls.py INDEX.json", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        doc = ROOT / DOC
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
            "coverage": "supplied-snapshot-subset-only-unverified",
            "input_sha256": hashlib.sha256(raw).hexdigest(),
            "source_document": DOC,
            "source_document_sha256": hashlib.sha256(doc.read_bytes()).hexdigest(),
            "other_driver_sha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in ("scripts/h55/vectors-tables/run_raw_parser.py", "scripts/h55/vectors-tables/raw_master_reconcile.py")},
            "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f"parser probe classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
