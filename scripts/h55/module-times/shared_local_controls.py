#!/usr/bin/env python3
"""Guard regression: shared translator local controls are mistaken for source adequacy or runnable runtime acceptance."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "tests/directruntime-20261104/shared-translator/"
DOC = "docs/feature-work/directruntime-shared-translator.md"
ROLES = {
    PREFIX + "AddressLocalControls.lean": ("address-local admission, tuple and environment controls", "artifacts/address/AddressLocals.ast.json"),
    PREFIX + "FixedByteLocalControls.lean": ("fixed-byte local admission and finite checker controls", "artifacts/fixed-bytes/FixedByteLocals.ast.json"),
    PREFIX + "NarrowLocalControls.lean": ("narrow-local admission and intrinsic obligation controls", "artifacts/h90/CanonicalReaderContract.ast.json"),
    PREFIX + "NarrowLocalRuntimeControls.lean": ("narrow-local intrinsic model and checker observations", "artifacts/h90/NarrowLocalRuntime.ast.json"),
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
        rows.append({"candidate": row, "role": ROLES[path][0], "source_document": DOC, "source_document_sha256": hashlib.sha256((root / DOC).read_bytes()).hexdigest(), "fixture_path": PREFIX + ROLES[path][1], "fixture_present": (root / PREFIX / ROLES[path][1]).is_file(), "fixture_sha256": hashlib.sha256((root / PREFIX / ROLES[path][1]).read_bytes()).hexdigest() if (root / PREFIX / ROLES[path][1]).is_file() else None,
            "driver": "handoff describes finite fixture-based controls; exact current invocation and result unverified",
            "inputs": "Lean imports and per-row AST fixture; workspace, fixture identities and toolchain unresolved",
            "effects": "Lean guards and diagnostics with finite model/checker observations; external driver effects unresolved",
            "expected_outcome": "current exit and output unverified; finite controls do not establish Source/ABI adequacy, native closure or module timing",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: shared_local_controls.py INDEX.json", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
            "coverage": "supplied-snapshot-subset-only-unverified",
            "limitations": "auxiliary inputs and handoff changes are not tracked by candidate drift; recheck before reuse",
            "input_sha256": hashlib.sha256(raw).hexdigest(),
            "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f"shared local control classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
