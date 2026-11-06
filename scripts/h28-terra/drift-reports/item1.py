#!/usr/bin/env python3
"""Report conservative module-map lexical candidates from supplied files."""
import json
import re
import sys


def report(data):
    files = data.get("files", [])
    if (not isinstance(files, list) or any(
        not isinstance(f, dict) or not isinstance(f.get("path"), str)
        or not isinstance(f.get("text"), str) for f in files
    ) or len({f["path"] for f in files}) != len(files)):
        return {"error": "invalid-or-duplicate-files"}
    maps = "\n".join(f["text"] for f in files if f["path"].startswith("docs/module-map") and f["path"].endswith(".md"))
    result = []
    for f in sorted(files, key=lambda f: f["path"]):
        path = f["path"]
        if not path.endswith(".lean"):
            continue
        module = path[:-5].replace("/", ".")
        library = ("Bridge" if path.startswith("Bridge/") else
                   "SolidityExamples" if path.startswith("Solidity/Examples/") else
                   "Solidity" if path.startswith("Solidity/") else "root-or-other")
        result.append({"path": path, "module": module, "library": library,
                       "mapTokenOccurrences": len(re.findall(r"(?<![\w.])" + re.escape(module) + r"(?![\w.])", maps)),
                       "verdict": "lexical-row-candidate-not-confirmed-drift"})
    return result


if __name__ == "__main__":
    json.dump(report(json.load(sys.stdin)), sys.stdout)
    print()
