#!/usr/bin/env python3
"""Guard regression: storage source conversion checks are counted as full Source elaboration or execution."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "tests/h62/item2/audit-v10-storage/"
DOC = "docs/feature-work/h62-2-audit-v10-storage.md"
ROLES = {
    "ArrayAccessWitnesses": "populated live-array access witnesses using symbolic-slot EVM execution",
    "SourceAstCompoundTypesControls": "compound type conversion and malformed/payable mapping-key refusals",
    "SourceAstCorrespondenceControls": "list correspondence algorithm controls",
    "SourceAstExpressionsControls": "existing LibraryTry AST expression conversion checks",
    "SourceAstStatementsControls": "existing LibraryTry AST statement conversion checks",
    "SourceAstTypesControls": "existing LibraryTry AST type conversion checks",
    "SourceAstUnitControls": "manual full-unit elaboration probe; known failure, acceptance remains open, not expected-failure pass",
    "SourceAstUnitResolutionControls": "unit conversion and catalogue resolution without body typing",
    "TargetWriteSequenceWitnesses": "target write-sequence joint-input witnesses",
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
            "driver": "audit handoff describes source controls; full-unit probe is manual and ungated; exact current invocation unresolved",
            "inputs": "Lean toolchain and imports; AST readers need fixture files; current workspace, cache and dependency products unresolved",
            "effects": "AST reader modules use IO.FS.readFile on LibraryTry fixtures or fixtureInputs; diagnostics and other effects depend on unresolved driver",
            "expected_outcome": "current exit and output unverified; manual full-unit failure is not an accepted expected-failure gate; no Source or physical/world adequacy established",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: v10_source_ast_controls.py INDEX.json", file=sys.stderr)
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
        print(f"V10 Source AST classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
