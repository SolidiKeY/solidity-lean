#!/usr/bin/env python3
"""Guard regression: primitive correspondence source claims are counted as current verified execution."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "tests/h62/item4/generic-primitive-packets/"
DOC = "docs/feature-work/h62-4-generic-primitive-packets.md"
ROLES = {
    "BitNotCorrespondence": "width-cleaned unsigned complement correspondence statements",
    "BitwiseCorrespondence": "bitwise AND, OR and XOR correspondence statements",
    "ComparisonCorrespondence": "signed and unsigned comparison correspondence statements",
    "ConstantCorrespondence": "typed literal correspondence and out-of-range refusals",
    "ShiftsCorrespondence": "unchecked uint256 shift correspondence and saturation",
    "SignedCastCorrespondence": "signed narrowing cast correspondence with destination wrapping",
    "SignedDivCorrespondence": "signed division, zero-divisor and minimum-overflow correspondence",
    "SignedModCorrespondence": "signed remainder and zero-divisor correspondence",
    "UnsignedCastCorrespondence": "strict-smaller-width unsigned narrowing cast correspondence",
    "UnsignedMulCorrespondence": "unchecked width-cleaned unsigned multiplication correspondence",
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
            "driver": "source and feature handoff state correspondence boundaries; exact current driver and invocation unresolved",
            "inputs": "Lean toolchain and imports; actual current workspace, cache and dependency products unresolved",
            "effects": "Lean diagnostics and axiom text; output artifact paths and side effects depend on unresolved driver",
            "expected_outcome": "current exit and output unverified; source statements do not establish full world, session, gas or fetched-EVM adequacy",
            "status": "static-reference-not-execution-acceptance"})
    return rows


def main():
    if len(sys.argv) != 2:
        print("usage: primitive_correspondence_extra.py INDEX.json", file=sys.stderr)
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
        print(f"primitive correspondence extra classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
