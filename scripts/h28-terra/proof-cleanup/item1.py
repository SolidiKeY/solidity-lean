#!/usr/bin/env python3
"""Report lexical simp/simpa candidates; owner review remains necessary."""
import json
import re
import sys


def lean_code(text):
    out = []
    i = 0
    depth = 0
    quote = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quote:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                quote = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            quote = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def analyze(data):
    files = data.get("files", [])
    if (not isinstance(files, list) or any(
        not isinstance(f, dict) or not isinstance(f.get("path"), str)
        or not isinstance(f.get("text"), str) for f in files
    ) or len({f["path"] for f in files}) != len(files)):
        return {"error": "invalid-or-duplicate-files"}
    result = []
    for f in sorted(files, key=lambda row: row["path"]):
        if not f["path"].endswith(".lean"):
            continue
        code = lean_code(f["text"])
        candidates = [{"line": code[:m.start()].count("\n") + 1, "token": m[0]}
                      for m in re.finditer(r"\b(?:simp|simpa)\b(?!\s+only\b)", code)]
        result.append({"path": f["path"], "candidates": candidates})
    return result


if __name__ == "__main__":
    json.dump(analyze(json.load(sys.stdin)), sys.stdout)
    print()
