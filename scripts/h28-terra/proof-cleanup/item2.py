#!/usr/bin/env python3
"""Group exact lexical normalized declaration tails, requiring owner review."""
import collections
import json
import re
import sys
from item1 import lean_code


def analyze(data):
    files = data.get("files", [])
    if (not isinstance(files, list) or any(
        not isinstance(f, dict) or not isinstance(f.get("path"), str)
        or not isinstance(f.get("text"), str) for f in files
    ) or len({f["path"] for f in files}) != len(files)):
        return {"error": "invalid-or-duplicate-files"}
    codes = {f["path"]: lean_code(f["text"]) for f in files if f["path"].endswith(".lean")}
    groups = collections.defaultdict(list)
    for path, code in sorted(codes.items()):
        declarations = list(re.finditer(r"(?m)^(?:private |protected )?(?:theorem|lemma|def|abbrev)\s+([\w.]+)", code))
        for i, match in enumerate(declarations):
            tail = code[match.end():declarations[i + 1].start() if i + 1 < len(declarations) else len(code)]
            normalized = re.sub(r"\s+", " ", tail).strip()
            if normalized:
                groups[normalized].append(path + ":" + match[1])
    return [{"path": path, "duplicateCandidates": sorted(
        names for names in groups.values()
        if len(names) > 1 and any(name.startswith(path + ":") for name in names)
    )} for path in sorted(codes)]


if __name__ == "__main__":
    json.dump(analyze(json.load(sys.stdin)), sys.stdout)
    print()
