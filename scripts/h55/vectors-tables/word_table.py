#!/usr/bin/env python3
"""Losslessly extract and reproduce frozen WordTable proof parts off Git.

The proof text is transcribed, not synthesized; Lean still checks every proof.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
AREA = Path("Solidity/Frontend/NumericLiteralProofs/WordTable")
MANIFEST = ROOT / "tests/h55/vectors-tables/word-table-manifest.json"
BASE = "4d3790eadb8a5212233bc7d5e345817476b2f590"
NAMES = [f"Part{i:02}.lean" for i in range(30)]
HEADING = re.compile(r"^theorem (table_prefix_(?:[0-9_]+|root)|table_other)\b", re.M)
FOOT = "\nend Solidity.Frontend.NumericLiteralProofs\n"

def sha(data): return hashlib.sha256(data).hexdigest()
def split(name, data):
    text = data.decode("utf-8")
    hits = list(HEADING.finditer(text))
    if len(hits) != len(re.findall(r"^theorem\s+", text, re.M)): raise ValueError(f"{name}: unrecognised theorem")
    if not hits or not text.endswith(FOOT): raise ValueError(f"{name}: heading or footer schema")
    header = text[:hits[0].start()]
    chunks = [text[m.start():hits[i+1].start() if i+1 < len(hits) else -len(FOOT)] for i,m in enumerate(hits)]
    rows = [{"name": m.group(1), "text": chunk} for m,chunk in zip(hits,chunks)]
    if len(set(r["name"] for r in rows)) != len(rows): raise ValueError("duplicate theorem")
    if header + "".join(r["text"] for r in rows) + FOOT != text: raise ValueError("lossy extraction")
    return {"header": header, "rows": rows}

def collect(root):
    actual = sorted(p.name for p in (root / AREA).glob("*.lean"))
    if actual != NAMES: raise ValueError("part inventory")
    return {name: split(name, (root / AREA / name).read_bytes()) for name in NAMES}

def render(records):
    if type(records) is not dict or list(records) != NAMES: raise ValueError("parts or order")
    output = {}
    for name in NAMES:
        part = records[name]
        if type(part) is not dict or set(part) != {"header", "rows"} or type(part["header"]) is not str or type(part["rows"]) is not list: raise ValueError("part schema")
        for row in part["rows"]:
            if type(row) is not dict or set(row) != {"name", "text"} or type(row["name"]) is not str or type(row["text"]) is not str: raise ValueError("row schema")
        data = (part["header"] + "".join(x["text"] for x in part["rows"]) + FOOT).encode()
        if split(name, data) != part: raise ValueError("declaration schema")
        output[name] = data
    return output

def manifest(records):
    outputs = render(records)
    return {"base": BASE, "files": {name: {"sha256": sha(outputs[name]), "theorems": [r["name"] for r in records[name]["rows"]]} for name in NAMES}}

def main():
    p = argparse.ArgumentParser()
    p.add_argument("mode", choices=("manifest", "extract", "check", "emit"))
    p.add_argument("data", nargs="?", type=Path)
    p.add_argument("--output", type=Path)
    a = p.parse_args()
    if (a.mode in ("extract", "check", "emit")) != (a.data is not None): p.error("data required for extract, check and emit")
    if (a.mode == "emit") != (a.output is not None): p.error("output required only for emit")
    original = collect(ROOT)
    if a.mode == "manifest":
        if MANIFEST.exists(): raise ValueError("manifest exists")
        MANIFEST.write_text(json.dumps(manifest(original), indent=2) + "\n")
        return
    expected = json.loads(MANIFEST.read_text())
    if manifest(original) != expected: raise ValueError("original differs from pinned manifest")
    if a.mode == "extract":
        if a.data.exists() or a.data.resolve().is_relative_to(ROOT): raise ValueError("bulk must be a new external file")
        a.data.write_text(json.dumps({"schema": 1, "parts": original}, ensure_ascii=False, separators=(",", ":")) + "\n")
        return
    data = json.loads(a.data.read_text())
    if type(data) is not dict or set(data) != {"schema", "parts"} or type(data["schema"]) is not int or data["schema"] != 1: raise ValueError("data schema")
    generated = render(data["parts"])
    if manifest(data["parts"]) != expected or any(generated[n] != (ROOT / AREA / n).read_bytes() for n in NAMES): raise ValueError("data differs from original")
    if a.mode == "emit":
        dest = a.output.resolve()
        if dest.is_relative_to(ROOT): raise ValueError("output must be external")
        dest.mkdir(parents=True, exist_ok=False)
        for name, content in generated.items(): (dest / name).write_bytes(content)
    print("PASS: 30 parts and 439 complete proof declarations reproduced")

if __name__ == "__main__": main()
