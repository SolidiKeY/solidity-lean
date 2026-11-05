#!/usr/bin/env python3
"""Retain every receipt line while extracting the specified Lake timings."""
import json
import re
import sys


def main(data):
    files = data.get("files", [])
    if (not isinstance(files, list)
            or any(not isinstance(f, dict) or not isinstance(f.get("path"), str)
                   or not isinstance(f.get("text"), str) for f in files)
            or len({f["path"] for f in files}) != len(files)):
        return {"error": "invalid-or-duplicate-files"}
    result = []
    for file in sorted(files, key=lambda f: f["path"]):
        records = []
        for number, line in enumerate(file["text"].splitlines(), 1):
            match = re.search(r"Built ([\w.]+).*\((\d+(?:\.\d+)?|\.\d+)(ms|s)\)", line)
            if match:
                records.append({"line": number, "module": match[1],
                                "seconds": float(match[2]) / (1000 if match[3] == "ms" else 1)})
            else:
                records.append({"line": number, "unparsed": line})
        result.append({"path": file["path"], "records": records})
    return result


if __name__ == "__main__":
    json.dump(main(json.load(sys.stdin)), sys.stdout)
    sys.stdout.write("\n")
