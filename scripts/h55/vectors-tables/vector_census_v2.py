#!/usr/bin/env python3
"""Census v2: layout-independent preservation of the frozen vector tuples.

Census v1 (`vector_census.py`, frozen and unchanged) authenticates the exact
source bytes of the per-theorem vector files. A family converted to a literal
row table (H379/H400) keeps every tuple but not those bytes. v2 extracts, per
family and in file order, each `(opcode, operands, expected)` tuple from either
layout and compares the ordered tuples with a digest frozen from the
v1-authenticated sources. Like v1 it is a census, not an EVM oracle; the Lean
kernel checks remain the evidence that each tuple holds.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MANIFEST = ROOT / "tests/h55/vectors-tables/vector-manifest-v2.json"
V1_BASE = "4d3790eadb8a5212233bc7d5e345817476b2f590"
FAMILIES = {
    "shifts": [f"Solidity/Yul/Checks/Shifts/Part{i:02}.lean" for i in range(4)],
    "arithmetic": [f"Solidity/Yul/Checks/Arithmetic/Part{i:02}.lean" for i in range(3)],
    "bytes": ["Solidity/Yul/Checks/Bytes.lean"],
    "powers": ["Solidity/Yul/Checks/Powers.lean"],
}
NAT = r"(?:0|[1-9][0-9]*)"
# v1 layout: one `theorem vNNNN` per tuple.
THEOREM = re.compile(rf"theorem v[0-9]{{4}} : \(Pure\.eval \.«([a-z]+)» \(fun (?:i|_) => (.+)\)\)\.val = ({NAT}) := by decide \+kernel")
ARG = re.compile(rf"if i\.val = ({NAT}) then word ({NAT}) else ")
TAIL = re.compile(rf"word ({NAT})")
# Row-table layout (binary rows, as in Solidity/Yul/Checks/Shifts/Part01-03).
ROW = re.compile(rf"  ⟨\.«([a-z]+)», ({NAT}), ({NAT}), ({NAT})⟩,?")

def operands(expr):
    args = []
    while m := ARG.match(expr):
        if int(m.group(1)) != len(args): raise ValueError("argument index")
        args.append(m.group(2)); expr = expr[m.end():]
    tail = TAIL.fullmatch(expr)
    if not tail: raise ValueError("argument tail")
    return [*args, tail.group(1)]

def tuples(path, text):
    """Ordered tuples of one file; any vector-like line outside the schemas fails."""
    rows = []
    for line in text.splitlines():
        if line.startswith("theorem v"):
            m = THEOREM.fullmatch(line)
            if not m: raise ValueError(f"{path}: unsupported theorem schema")
            rows.append((m.group(1), operands(m.group(2)), m.group(3)))
        elif line.startswith("  ⟨"):
            m = ROW.fullmatch(line)
            if not m: raise ValueError(f"{path}: unsupported row schema")
            rows.append((m.group(1), [m.group(2), m.group(3)], m.group(4)))
    return rows

def digest(rows):
    return hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest()

def census(root):
    out = {}
    for family, paths in FAMILIES.items():
        rows = [r for p in paths for r in tuples(p, (root / p).read_text(encoding="utf-8"))]
        out[family] = {"count": len(rows), "sha256": digest(rows)}
    return out

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--root", type=Path, default=ROOT)
    p.add_argument("--create-manifest", action="store_true",
                   help="freeze from --root, which v1 must authenticate byte for byte")
    a = p.parse_args()
    actual = census(a.root)
    if a.create_manifest:
        sys.path.insert(0, str(Path(__file__).parent))
        import vector_census as v1
        if v1.census(a.root) != json.loads(v1.MANIFEST.read_text())["files"]:
            raise SystemExit("FAIL: --root is not the v1-authenticated source")
        MANIFEST.write_text(json.dumps({"v1_base": V1_BASE, "families": actual}, indent=2) + "\n")
        return
    expected = json.loads(MANIFEST.read_text())
    if expected["v1_base"] != V1_BASE or actual != expected["families"]:
        raise SystemExit("FAIL: vector tuples differ from the frozen v1 tuples")
    print(f"PASS: {len(actual)} families, {sum(x['count'] for x in actual.values())} tuples; ordered tuples match v1")

if __name__ == "__main__":
    main()
