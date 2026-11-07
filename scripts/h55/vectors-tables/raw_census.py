#!/usr/bin/env python3
"""Pinned textual Raw inventory. This is not a Lean parser or proof of coverage."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
AREA = Path("Solidity/Yul")
MANIFEST = ROOT / "tests/h55/vectors-tables/raw-manifest.json"
BASE = "4d3790eadb8a5212233bc7d5e345817476b2f590"
DECL = re.compile(r"^inductive\s+([A-Za-z_][A-Za-z0-9_]*)\b")
TOP = re.compile(r"^(?:def|theorem|lemma|structure|inductive|abbrev|namespace|end|private|@\[)\b")
CTOR = re.compile(r"^  \|\s+([A-Za-z_][A-Za-z0-9_]*)\b")
BRANCH = re.compile(r"^\s*(?:\||case\s+)")

def sha(data): return hashlib.sha256(data).hexdigest()
def scan(path, data):
    text = data.decode("utf-8")
    families, branches = [], []
    active = None
    for number, line in enumerate(text.splitlines(), 1):
        match = DECL.match(line)
        if match:
            active = {"name": match.group(1), "line": number, "constructors": []}
            families.append(active)
        elif active is not None and TOP.match(line):
            active = None
        if active is not None:
            match = CTOR.match(line)
            if match: active["constructors"].append({"name": match.group(1), "line": number})
        if BRANCH.match(line): branches.append({"line": number, "text": line})
    if any(not family["constructors"] for family in families): raise ValueError(f"{path}: inductive with no recognized constructors")
    return {"sha256": sha(data), "families": families, "branches": branches}

def collect(root):
    files = sorted((root / AREA).glob("Raw*.lean"))
    if len(files) != 102: raise ValueError("expected 102 Raw files")
    return {p.name: scan(p.name, p.read_bytes()) for p in files}

def summary(records):
    return {"base": BASE, "files": {name: {"sha256": v["sha256"], "families": v["families"], "branch_count": len(v["branches"]), "branch_sha256": sha(json.dumps(v["branches"], ensure_ascii=False, separators=(",", ":")).encode())} for name,v in records.items()}}

def main():
    p = argparse.ArgumentParser(); p.add_argument("mode", choices=("manifest", "extract", "check")); p.add_argument("data", nargs="?", type=Path); a=p.parse_args()
    records=collect(ROOT)
    if a.mode == "manifest":
        if a.data is not None or MANIFEST.exists(): raise ValueError("manifest already exists or unexpected argument")
        MANIFEST.write_text(json.dumps(summary(records), indent=2) + "\n"); return
    if summary(records) != json.loads(MANIFEST.read_text()): raise ValueError("frozen source census differs")
    if a.mode == "extract":
        if a.data is None or a.data.exists() or a.data.resolve().is_relative_to(ROOT): raise ValueError("new external data path required")
        a.data.write_text(json.dumps({"schema": 1, "files": records}, ensure_ascii=False, separators=(",", ":")) + "\n"); return
    if a.data is None: raise ValueError("data required")
    data=json.loads(a.data.read_text())
    if type(data) is not dict or set(data) != {"schema", "files"} or type(data["schema"]) is not int or data["schema"] != 1 or data["files"] != records: raise ValueError("data inventory differs")
    print(f"PASS: {len(records)} files, {sum(len(v['families']) for v in records.values())} inductives, {sum(len(f['constructors']) for v in records.values() for f in v['families'])} recognized constructors, {sum(len(v['branches']) for v in records.values())} candidate branch lines")

if __name__ == "__main__": main()
