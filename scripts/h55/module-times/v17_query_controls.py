#!/usr/bin/env python3
"""Guard regression: V17 query templates are mistaken for semantic closure or timing acceptance."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "scripts/"
ROLES = {
    PREFIX + "roadmap-v17-creation-try-query.lean": ("creation-try producer observation and native replay query body", ["roadmap-v17-creation-try.py"]),
    PREFIX + "roadmap-v17-kernel-query.lean": ("bounded above-core kernel metadata query template", ["roadmap-v17-kernel.py", "roadmap-v17-loops.py", "roadmap-v17-memory-calls.py", "roadmap-v17-creation-try.py"]),
    PREFIX + "roadmap-v17-memory-calls-query.lean": ("published memory-call example observation query body", ["roadmap-v17-memory-calls.py"]),
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
            "driver": "listed Python drivers compose query templates or bodies; current invocation, generated source and outcome unverified",
            "inputs": "published producer data, template substitutions and Lean environment; actual inputs, workspace, build products and toolchain unresolved",
            "effects": "queries emit framed JSON or diagnostics; drivers may generate source, logs and JSON output, start a Docker container and write /workspace/scratch/v17-unresolved-container.json",
            "expected_outcome": "current exit and output unverified; observations do not establish semantic premises, release closure or module timing",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: v17_query_controls.py INDEX.json", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
            "coverage": "supplied-snapshot-subset-only-unverified",
            "limitations": "candidate drift does not track driver or producer input changes; recheck hashes and inputs before reuse",
            "input_sha256": hashlib.sha256(raw).hexdigest(),
            "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f"V17 query classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
