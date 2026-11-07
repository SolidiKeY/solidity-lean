#!/usr/bin/env python3
"""Guard regression: control-tuple fixtures are mistaken for source adequacy or authenticated module timing."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "tests/directruntime-20261104/control-tuples/"
DOC = "docs/feature-work/directruntime-control-tuples.md"
ROLES = {
    PREFIX + "ObligationControls.lean": ("trusted-verifier relative box/diamond and refusal checks", ["Obligations.ast.json"]),
    PREFIX + "ProductionControls.lean": ("Lean-hosted DirectRuntime API status controls", ["Obligations.ast.json"]),
    PREFIX + "ProofAudit.lean": ("Lean signature checks and axiom inspection", []),
    PREFIX + "RuntimeProbe.lean": ("intrinsic model execution fixture and refusal probe", ["Controls.ast.json", "FailureAlias.ast.json"]),
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
        rows.append({"candidate": row, "role": ROLES[path][0], "source_document": DOC, "source_document_sha256": hashlib.sha256((root / DOC).read_bytes()).hexdigest(), "fixture_sha256": {PREFIX + name: hashlib.sha256((root / PREFIX / name).read_bytes()).hexdigest() for name in ROLES[path][1]},
            "driver": "handoff describes per-file controls, audits and native fixture checks; exact current invocation and outcome unverified",
            "inputs": "Lean imports and the listed JSON fixtures when applicable; current workspace, dependencies and toolchain unresolved",
            "effects": "Lean checks emit diagnostics; native fixture probe prints model results and refusal observations; external runner effects unresolved",
            "expected_outcome": "current exit and output unverified; fixture controls do not establish Source/EVM adequacy or module timing",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: control_tuple_controls.py INDEX.json", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
            "coverage": "supplied-snapshot-subset-only-unverified",
            "limitations": "candidate drift does not track fixture or document changes; recheck embedded hashes before reuse",
            "input_sha256": hashlib.sha256(raw).hexdigest(),
            "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f"control tuple classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
