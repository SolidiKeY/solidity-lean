#!/usr/bin/env python3
"""Guard regression: read-only compiler audit helpers are mistaken for complete witnesses or timing acceptance."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "scripts/h62/item2/audit-evm-compiler/"
ROLES = {
    PREFIX + "Closed.lean": ("inspects requested direct closed equality theorem types and axiom sets", ["closed_census.py"]),
    PREFIX + "Inspect.lean": ("censuses requested theorem metadata, binders and axioms for one module", ["inspect.py", "inspect_bridge.py"]),
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
        rows.append({"candidate": row, "role": ROLES[path][0], "driver_sha256": {PREFIX + name: hashlib.sha256((root / PREFIX / name).read_bytes()).hexdigest() for name in ROLES[path][1]},
            "driver": "listed Python drivers invoke the corresponding Lean helper serially; current invocation and outcome unverified",
            "inputs": "names file, one requested module and imported Lean environment; actual names, workspace, build products and toolchain unresolved",
            "effects": "Lean helper reads names and emits JSON rows to stdout; drivers create names, logs and JSON evidence at caller-selected paths",
            "expected_outcome": "current exit and output unverified; inspection does not establish complete witness coverage, semantic success or module timing",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: evm_audit_helpers.py INDEX.json", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
            "coverage": "supplied-snapshot-subset-only-unverified",
            "limitations": "candidate drift does not track driver or names-file changes; recheck hashes and inputs before reuse",
            "input_sha256": hashlib.sha256(raw).hexdigest(),
            "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f"EVM audit helper classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
