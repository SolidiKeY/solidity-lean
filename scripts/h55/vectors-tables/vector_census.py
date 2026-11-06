#!/usr/bin/env python3
"""Audit the full frozen vector declaration inventory without modifying inputs.

The manifest authenticates complete source bytes. The parsed rows are a census,
not an independent EVM oracle or a replacement for Lean kernel checks.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MANIFEST = ROOT / "tests/h55/vectors-tables/vector-manifest.json"
PATHS = [*(f"Solidity/Yul/Checks/Shifts/Part{i:02}.lean" for i in range(4)),
         *(f"Solidity/Yul/Checks/Arithmetic/Part{i:02}.lean" for i in range(3)),
         "Solidity/Yul/Checks/Bytes.lean", "Solidity/Yul/Checks/Powers.lean"]
ROW = re.compile(r"theorem (v[0-9]{4}) : \(Pure\.eval .«([a-z]+)» \(fun (?:i|_) => (.+)\)\)\.val = ([0-9]+) := by decide \+kernel")
ARGS = re.compile(r"(?:if i\.val = ([0-9]+) then word ([0-9]+) else )*word ([0-9]+)")

def audit(path, data):
    text = data.decode("utf-8")
    rows = []
    for line in text.splitlines():
        if line.startswith("theorem "):
            m = ROW.fullmatch(line)
            if not m or not ARGS.fullmatch(m.group(3)):
                raise ValueError(f"{path}: unsupported declaration schema")
            rows.append(m.group(1))
    if not rows or len(rows) != len(set(rows)):
        raise ValueError(f"{path}: missing or duplicate declarations")
    nums = [int(x[1:]) for x in rows]
    if nums != list(range(nums[0], nums[0] + len(nums))):
        raise ValueError(f"{path}: missing, extra or reordered declaration")
    return {"sha256": hashlib.sha256(data).hexdigest(), "count": len(rows),
            "first": rows[0], "last": rows[-1]}

def census(root):
    return {p: audit(p, (root / p).read_bytes()) for p in PATHS}

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--root", type=Path, default=ROOT)
    p.add_argument("--create-manifest", action="store_true")
    a = p.parse_args()
    actual = census(a.root)
    if a.create_manifest:
        MANIFEST.write_text(json.dumps({"base": "4d3790eadb8a5212233bc7d5e345817476b2f590", "files": actual}, indent=2) + "\n")
    else:
        expected = json.loads(MANIFEST.read_text())
        if expected["base"] != "4d3790eadb8a5212233bc7d5e345817476b2f590" or actual != expected["files"]:
            raise SystemExit("FAIL: inventory or source bytes differ from frozen manifest")
        print(f"PASS: {len(actual)} files, {sum(x['count'] for x in actual.values())} declarations; source bytes match")

if __name__ == "__main__":
    main()
