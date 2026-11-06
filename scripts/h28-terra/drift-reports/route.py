#!/usr/bin/env python3
"""Conservative lexical owner hints; unlinked files remain unassigned."""
import json
import re
import sys


def route(data):
    owners = {row["id"]: row for row in data["ownership"]}
    output = []
    for f in sorted(data["files"], key=lambda row: row["path"]):
        if not f["path"].endswith(".lean"):
            continue
        text = f["path"] + "\n" + f["text"]
        ids = sorted(i for i in owners if re.search(r"(?<![\w.-])" + re.escape(i) + r"(?![\w.-])", text))
        output.append({"path": f["path"], "ownerHints": [owners[i] for i in ids],
                       "verdict": "lexical-hint-owner-review-required" if ids else "unassigned-owner-review-required"})
    return output


if __name__ == "__main__":
    json.dump(route(json.load(sys.stdin)), sys.stdout)
    print()
