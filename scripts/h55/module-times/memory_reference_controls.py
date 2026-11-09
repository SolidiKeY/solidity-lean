#!/usr/bin/env python3
"""Guard regression: memory-reference developer controls are mistaken for runnable native or source adequacy acceptance."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "tests/directruntime-20261104/memory-references/"
DOC = "docs/feature-work/directruntime-memory-references.md"
ROLES = {
    PREFIX + "Admission.lean": ("developer AST admission and intrinsic model checks", DOC),
    PREFIX + "KernelControls.lean": ("focused intrinsic calculus kernel development controls", DOC),
    PREFIX + "KernelMatrix.lean": ("generated fixture-body intrinsic calculus matrix and axiom reports", DOC),
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
            "driver": "handoff describes developer and kernel controls; exact current invocation and result unverified",
            "inputs": "Lean imports; Admission reads absent evidence/admission-inputs.json and listed files; KernelMatrix imports local KernelControls; current workspace and toolchain unresolved",
            "effects": "Admission writes model-results.json and model-results.composed.json under evidence; generator writes KernelMatrix.lean; diagnostics and driver effects otherwise unresolved",
            "expected_outcome": "current exit and output unverified; development controls do not establish source adequacy, native/browser acceptance or module timing",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: memory_reference_controls.py INDEX.json", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
            "coverage": "supplied-snapshot-subset-only-unverified",
            "limitations": "auxiliary inputs and document changes are not tracked by candidate drift; recheck before reuse",
            "generator_sha256": hashlib.sha256((ROOT / PREFIX / "generate-kernel-matrix.py").read_bytes()).hexdigest(),
            "input_presence": {name: (ROOT / PREFIX / name).is_file() for name in ("manifest.json", "evidence/admission-inputs.json")},
            "input_sha256": hashlib.sha256(raw).hexdigest(),
            "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f"memory reference classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
