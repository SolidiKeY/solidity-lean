#!/usr/bin/env python3
"""Authenticate built-in Lean parser node spans for the frozen Raw inputs.

This records syntax only. The probe does not elaborate project imports or prove
coverage of semantic execution cases.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
import raw_census as raw

MANIFEST = raw.ROOT / "tests/h55/vectors-tables/raw-syntax-manifest.json"
NODE = re.compile(r"NODE (Lean\.Parser\.(?:Command\.ctor|Term\.matchAlt|Tactic\.(?:inductionAlt|case|cases|induction))) some \{ byteIdx := ([0-9]+) \} some \{ byteIdx := ([0-9]+) \}")

def sha(data): return hashlib.sha256(data).hexdigest()
def parse_log(text, root=raw.ROOT):
    source = raw.collect(root)
    if raw.summary(source) != json.loads(raw.MANIFEST.read_text()): raise ValueError("Raw inputs differ from frozen manifest")
    names = list(source); lines = iter(text.splitlines()); result = {}
    for name in names:
        path = "Solidity/Yul/" + name
        if next(lines, None) != "FILE " + path: raise ValueError("file inventory or order")
        data = (root / raw.AREA / name).read_bytes(); nodes = []
        for line in lines:
            if line == "END " + path: break
            m = NODE.fullmatch(line)
            if not m: raise ValueError("invalid node schema or truncated file")
            kind, start, end = m.group(1), int(m.group(2)), int(m.group(3))
            if not 0 <= start < end <= len(data): raise ValueError("invalid source span")
            nodes.append({"kind": kind, "start": start, "end": end, "source_sha256": sha(data[start:end])})
        else: raise ValueError("missing file end")
        result[name] = nodes
    if next(lines, None) is not None: raise ValueError("extra log entries")
    return result

def summary(data):
    return {"base": raw.BASE, "files": {name: {"count": len(nodes), "sha256": sha(json.dumps(nodes, separators=(",", ":")).encode())} for name, nodes in data.items()}}

def main():
    p=argparse.ArgumentParser(); p.add_argument("mode", choices=("manifest", "extract", "check")); p.add_argument("log", type=Path); p.add_argument("data", nargs="?", type=Path); a=p.parse_args()
    nodes = parse_log(a.log.read_text())
    if a.mode == "manifest":
        if a.data is not None or MANIFEST.exists(): raise ValueError("manifest exists or unexpected data")
        MANIFEST.write_text(json.dumps(summary(nodes), indent=2) + "\n"); return
    if summary(nodes) != json.loads(MANIFEST.read_text()): raise ValueError("node inventory differs")
    if a.data is None: raise ValueError("data required")
    if a.mode == "extract":
        if a.data.exists() or a.data.resolve().is_relative_to(raw.ROOT): raise ValueError("new external path required")
        a.data.write_text(json.dumps({"schema": 1, "files": nodes}, separators=(",", ":")) + "\n"); return
    data = json.loads(a.data.read_text())
    if type(data) is not dict or set(data) != {"schema", "files"} or type(data["schema"]) is not int or data["schema"] != 1 or data["files"] != nodes: raise ValueError("data differs")
    print(f"PASS: {len(nodes)} files, {sum(map(len, nodes.values()))} selected Lean parser nodes")

if __name__ == "__main__": main()
