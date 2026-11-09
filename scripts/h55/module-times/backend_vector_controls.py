#!/usr/bin/env python3
"""Guard regression: bounded backend vector exports are mistaken for runtime validation or general proofs."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
ROLES = {
    "tests/backend-environment/Emit.lean": ("backend environment instruction vectors encoded as JSON", "docs/feature-work/backend-environment-lowering.md"),
    "tests/creation-artifacts/Export.lean": ("creation artifact payloads and expected outputs emitted as JSON lines", "docs/feature-work/backend-creation-artifacts.md"),
    "tests/failure-emission/Export.lean": ("bounded failure-emitter encoded programs and payloads emitted as JSON lines", "docs/feature-work/backend-failure-emission.md"),
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
            "driver": "handoff documents cite finite external vector harnesses; exact current invocation and successful replay remain unverified",
            "inputs": "Lean imports and fixed in-source vector values; actual workspace, dependencies and toolchain identity unresolved",
            "effects": "Lean #eval emits vector data to stdout; downstream harnesses or redirection may write artifacts",
            "expected_outcome": "current exit and output unverified; finite external vectors do not establish whole-program proofs or module timing",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: backend_vector_controls.py INDEX.json", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
            "coverage": "supplied-snapshot-subset-only-unverified",
            "input_sha256": hashlib.sha256(raw).hexdigest(),
            "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f"backend vector classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
