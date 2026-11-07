#!/usr/bin/env python3
"""Account for Raw source pipe and case tokens outside comments and strings.

This lexical inventory includes non-case uses and is not Lean semantic analysis.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
import raw_census as raw

MANIFEST = raw.ROOT / "tests/h55/vectors-tables/raw-tokens-manifest.json"

def tokens(text):
    result = []; i = 0; line = 1; column = 1; depth = 0; quoted = False
    while i < len(text):
        ch = text[i]; pair = text[i:i+2]
        if depth:
            if pair == "/-": depth += 1; step = 2
            elif pair == "-/": depth -= 1; step = 2
            else: step = 1
        elif quoted:
            if ch == "\\":
                if i + 1 >= len(text): raise ValueError("unterminated escape")
                step = 2
            else:
                if ch == "\"": quoted = False
                step = 1
        elif pair == "/-": depth = 1; step = 2
        elif pair == "--":
            end = text.find("\n", i)
            step = len(text) - i if end < 0 else end - i
        elif ch == "\"": quoted = True; step = 1
        else:
            if ch == "|": result.append({"kind": "pipe", "line": line, "column": column})
            elif text.startswith("case", i) and (i == 0 or not (text[i-1].isalnum() or text[i-1] in "_\x27")) and (i+4 == len(text) or not (text[i+4].isalnum() or text[i+4] in "_\x27")):
                result.append({"kind": "case", "line": line, "column": column})
            step = 1
        segment = text[i:i+step]
        n = segment.count("\n")
        if n: line += n; column = len(segment.rsplit("\n", 1)[-1]) + 1
        else: column += step
        i += step
    if depth or quoted: raise ValueError("unclosed comment or string")
    return result

def inventory(root):
    files = raw.collect(root)
    if raw.summary(files) != json.loads(raw.MANIFEST.read_text()): raise ValueError("frozen Raw sources differ")
    return {name: tokens((root / raw.AREA / name).read_text()) for name in files}

def digest(data): return hashlib.sha256(data).hexdigest()
def summary(data):
    return {"base": raw.BASE, "files": {name: {"count": len(items), "sha256": digest(json.dumps(items, separators=(",", ":")).encode())} for name, items in data.items()}}

def main():
    p = argparse.ArgumentParser(); p.add_argument("mode", choices=("manifest", "extract", "check")); p.add_argument("data", nargs="?", type=Path); a=p.parse_args()
    value = inventory(raw.ROOT)
    if a.mode == "manifest":
        if a.data is not None or MANIFEST.exists(): raise ValueError("manifest exists or unexpected data")
        MANIFEST.write_text(json.dumps(summary(value), indent=2) + "\n"); return
    if summary(value) != json.loads(MANIFEST.read_text()): raise ValueError("token manifest differs")
    if a.data is None: raise ValueError("data required")
    if a.mode == "extract":
        if a.data.exists() or a.data.resolve().is_relative_to(raw.ROOT): raise ValueError("new external path required")
        a.data.write_text(json.dumps({"schema": 1, "files": value}, separators=(",", ":")) + "\n"); return
    data = json.loads(a.data.read_text())
    if type(data) is not dict or set(data) != {"schema", "files"} or type(data["schema"]) is not int or data["schema"] != 1 or data["files"] != value: raise ValueError("token data differs")
    count = sum(len(items) for items in value.values())
    print(f"PASS: {len(value)} source files and {count} lexical pipe/case occurrences")

if __name__ == "__main__": main()
