#!/usr/bin/env python3
"""Index lexical declaration occurrences; public/dynamic references need review."""
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
    occurrences = collections.Counter(re.findall(r"[\w.]+", "\n".join(codes.values())))
    result = []
    for path, code in sorted(codes.items()):
        names = re.findall(r"(?m)^(?:private |protected )?(?:theorem|lemma|def|abbrev)\s+([\w.]+)", code)
        result.append({"path": path, "declarations": [
            {"name": name, "lexicalOccurrences": occurrences[name],
             "verdict": "candidate-only-public-and-dynamic-review-required"}
            for name in names
        ]})
    return result


if __name__ == "__main__":
    json.dump(analyze(json.load(sys.stdin)), sys.stdout)
    print()
