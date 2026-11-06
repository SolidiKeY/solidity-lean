#!/usr/bin/env python3
"""Lexical census of named packet panic declarations and G25 reservations."""
import argparse
import fnmatch
import json
import pathlib
import re

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


def mask_comments_and_strings(source):
    """Mask nested comments, line comments, and strings without shifting lines."""
    chars = list(source)
    i, depth, string = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                chars[i:i + 2] = "  "
                i += 2
            elif pair == "-/":
                depth -= 1
                chars[i:i + 2] = "  "
                i += 2
            else:
                if source[i] != "\n":
                    chars[i] = " "
                i += 1
        elif string:
            if source[i] == "\\" and i + 1 < len(source):
                chars[i] = " "
                if source[i + 1] != "\n":
                    chars[i + 1] = " "
                i += 2
            else:
                if source[i] == chr(34):
                    string = False
                if source[i] != "\n":
                    chars[i] = " "
                i += 1
        elif pair == "--":
            while i < len(source) and source[i] != "\n":
                chars[i] = " "
                i += 1
        elif pair == "/-":
            depth = 1
            chars[i:i + 2] = "  "
            i += 2
        elif source[i] == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
            char = re.match(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|.)|[^'\\\n])'", source[i:])
            if char:
                end = i + len(char.group())
                chars[i:end] = " " * (end - i)
                i = end
            else:
                i += 1
        elif source[i] == chr(34):
            string = True
            chars[i] = " "
            i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError("unterminated comment or string")
    masked = "".join(chars)
    i = 0
    while i < len(masked):
        if masked[i:i + 2] != "@[":
            i += 1
            continue
        start = i
        depth = 1
        i += 2
        while i < len(masked) and depth:
            if masked[i] == "[":
                depth += 1
            elif masked[i] == "]":
                depth -= 1
            i += 1
        if depth:
            raise ValueError("unterminated attribute")
        for j in range(start, i):
            if masked[j] != "\n":
                chars[j] = " "
    return "".join(chars)
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
