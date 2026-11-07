#!/usr/bin/env python3
"""Index the coordinator's frozen 19-item audit without inferring ownership."""
import argparse
import hashlib
import json
import re
from pathlib import Path

AUDIT_SHA256 = "31ab16906906a9b22fd28700aacc72d2ee0ffe81cea723ae209eb28e5299286a"

def index(data):
    actual = hashlib.sha256(data).hexdigest()
    if actual != AUDIT_SHA256:
        raise ValueError("audit SHA256 does not match the frozen coordinator input")
    text = data.decode("utf-8")
    entries = re.findall(r"(?m)^(\d+)\. ([^\n]+)$", text)
    if [int(n) for n, _ in entries] != list(range(1, 20)):
        raise ValueError("expected exactly the ordered audit items 1 through 19")
    return {"audit_sha256": actual, "items": [
        {"id": int(n), "source_text": content,
         "ownership": "requires-live-coordinator-verification",
         "unowned_mechanical_opportunity": "not-established"}
        for n, content in entries]}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("audit", type=Path)
    args = parser.parse_args()
    try:
        report = index(args.audit.read_bytes())
    except (OSError, UnicodeError, ValueError) as exc:
        parser.exit(1, "audit index: " + str(exc) + "\n")
    print(json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2))

if __name__ == "__main__":
    main()
