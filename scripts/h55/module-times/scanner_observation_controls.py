#!/usr/bin/env python3
"""Guard regression: scanner observations are counted as global source or ownership proofs."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "tests/h62/item1/duplication-scanner/"
DOC = "docs/feature-work/h62-1-duplication-scanner.md"
ROLES = {
    "ASTSourceBinding": "enumerates visible AST constants and direct source ranges",
    "HeaderImports": "parses Lean headers without loading or executing project modules",
    "KeySortSourceBinding": "enumerates visible KeySort constants and direct source ranges",
    "MetadataFingerprintV2": "preserves supported expression metadata with explicit syntax refusals",
    "ScopeMetadataObservation": "observes visible Scope constants and metadata-aware fingerprints",
    "ScopeSourceBinding": "enumerates visible Scope constants and direct source ranges",
    "SignatureKernelCensus": "enumerates constants visible in the imported signature fixture",
    "SignatureSourceLocations": "reports direct declaration ranges for visible imported fixture constants",
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
            "driver": "scanner handoff and source record isolated observations; exact current invocation unresolved",
            "inputs": "Lean toolchain and imports; actual current workspace, cache and dependency products unresolved",
            "effects": "Lean diagnostics and axiom text; output artifact paths and side effects depend on unresolved driver",
            "expected_outcome": "current exit and output unverified; no global source, ownership or body-equivalence coverage claimed",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: scanner_observation_controls.py INDEX.json", file=sys.stderr)
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
        print(f"scanner observation classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
