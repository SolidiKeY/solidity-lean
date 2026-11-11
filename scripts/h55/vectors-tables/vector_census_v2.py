#!/usr/bin/env python3
"""Census v2: layout-independent preservation of the frozen vector tuples.

Census v1 (`vector_census.py`, frozen and unchanged) authenticates the exact
source bytes of the per-theorem vector files. A family converted to a literal
row table (H379/H400) keeps every tuple but not those bytes. v2 extracts, per
family and in file order, each `(opcode, operands, expected)` tuple from either
layout and compares the ordered tuples with a digest frozen from the
v1-authenticated sources (`--create-manifest` re-checks that link; a normal run
trusts the committed manifest). For a converted family it also requires the
registered list assembly and one well-formed list per row file, and rejects
vector-like lines it would otherwise skip. Like v1 it is a census, not an EVM
oracle; the Lean kernel checks remain the evidence that each tuple holds.
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
# Row-table layout (binary rows, as in Solidity/Yul/Checks/Shifts/Part01-03):
# exactly one list per row file, opened by OPEN and closed by a line `]`, with
# one row per line and nothing else inside.
OPEN = re.compile(r"noncomputable def ([A-Za-z]+) : List Row := \[")
ROW = re.compile(rf"  ⟨\.«([a-z]+)», ({NAT}), ({NAT}), ({NAT})⟩,?")
# A converted family's list must be assembled exactly as below, in FAMILIES order.
TABLES = {
    "shifts": ("Solidity/Yul/Checks/Shifts.lean",
               "noncomputable def rows : List Row := shlRows ++ shrRows ++ sarRows",
               {"Solidity/Yul/Checks/Shifts/Part01.lean": "shlRows",
                "Solidity/Yul/Checks/Shifts/Part02.lean": "shrRows",
                "Solidity/Yul/Checks/Shifts/Part03.lean": "sarRows"}),
}

def operands(expr):
    args = []
    while m := ARG.match(expr):
        if int(m.group(1)) != len(args): raise ValueError("argument index")
        args.append(m.group(2)); expr = expr[m.end():]
    tail = TAIL.fullmatch(expr)
    if not tail: raise ValueError("argument tail")
    return [*args, tail.group(1)]

def tuples(path, text, table=None):
    """Ordered `(opcode, operands, expected)` tuples of one file.

    Fails on a vector-like line (`theorem vNNNN` anywhere, or `⟨.«`) that is
    not a schema row in its place: inside a block comment, indented, outside
    the single row list, or in a file mixing both layouts. `table` names the
    one list a row file must hold."""
    rows, lists, depth, inside, kinds = [], [], 0, None, set()
    for line in text.splitlines():
        vectorish = re.search(r"theorem v[0-9]{4}", line) or "⟨.«" in line
        if vectorish and depth: raise ValueError(f"{path}: vector inside a comment")
        if inside is not None:
            if line == "]":
                inside = None
            else:
                m = ROW.fullmatch(line)
                if not m: raise ValueError(f"{path}: unsupported row schema")
                rows.append((m.group(1), [m.group(2), m.group(3)], m.group(4))); kinds.add("row")
            continue
        if m := OPEN.fullmatch(line):
            if lists: raise ValueError(f"{path}: more than one row list")
            lists.append(m.group(1)); inside = m.group(1)
        elif vectorish:
            m = THEOREM.fullmatch(line)
            if not m: raise ValueError(f"{path}: unsupported theorem schema")
            rows.append((m.group(1), operands(m.group(2)), m.group(3))); kinds.add("theorem")
        depth += line.count("/-") - line.count("-/")
    if inside is not None: raise ValueError(f"{path}: unterminated row list")
    if len(kinds) > 1: raise ValueError(f"{path}: mixed layouts")
    if table is not None and lists != [table]: raise ValueError(f"{path}: expected row list {table}")
    if table is None and lists: raise ValueError(f"{path}: unexpected row list")
    return rows

def digest(rows):
    return hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest()

def family_rows(root, family):
    paths = FAMILIES[family]
    texts = {p: (root / p).read_text(encoding="utf-8") for p in paths}
    converted = any(OPEN.search(t) for t in texts.values())
    tables = {}
    if converted:
        if family not in TABLES: raise ValueError(f"{family}: unregistered row-table layout")
        assembly, line, tables = TABLES[family]
        if (root / assembly).read_text(encoding="utf-8").splitlines().count(line) != 1:
            raise ValueError(f"{assembly}: family list is not assembled as registered")
    return [r for p in paths for r in tuples(p, texts[p], tables.get(p))]

def census(root):
    out = {}
    for family in FAMILIES:
        rows = family_rows(root, family)
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
