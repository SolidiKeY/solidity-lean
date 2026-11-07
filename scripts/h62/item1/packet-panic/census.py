#!/usr/bin/env python3
"""Lexical census of named packet panic declarations and G25 reservations."""
import argparse
import fnmatch
import json
import pathlib
import re
from lexical_mask import mask_comments_and_strings

parser = argparse.ArgumentParser()
parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path.cwd())
parser.add_argument("--ownership", type=pathlib.Path, required=True)
args = parser.parse_args()
root = args.root.resolve()
registry = json.loads(args.ownership.read_text())
items = registry["items"]
pattern = re.compile(
    r"^[ \t]*(?:(?:private|protected)[ \t]+)?"
    r"theorem[ \t\n]+(exact_panic_bytes|panic_not_truncated|exact_panic|panic_not_empty)(?![\w'.!?])", re.M)


records = []
scan_root = root / "Solidity/Backend/PrimitivePackets"
if not scan_root.is_dir():
    parser.error(f"missing scan root: {scan_root}")
for path in sorted(scan_root.rglob("*.lean")):
    rel = path.relative_to(root).as_posix()
    source = path.read_text()
    try:
        masked = mask_comments_and_strings(source)
    except ValueError as error:
        parser.error(f"{rel}: {error}")
    matches = list(pattern.finditer(masked))
    if not matches:
        continue
    owners = []
    for item in items:
        if not item.get("id", "").startswith("G25-"):
            continue
        for scope in item.get("writeScope", "").split(";"):
            scope = scope.strip()
            if fnmatch.fnmatchcase(rel, scope):
                owners.append({"id": item["id"], "owner": item.get("owner"), "status": item.get("status")})
                break
    for match in matches:
        records.append({"file": rel, "line": source.count("\n", 0, match.start(1)) + 1,
                        "declaration": match.group(1), "g25_reservations": owners})
print(json.dumps({"method": "lexical candidates only; empty G25 matches do not establish ownership or H55 eligibility", "registry_master_head": registry.get("masterHead"), "declarations": records}, indent=2))
