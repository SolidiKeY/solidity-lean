#!/usr/bin/env python3
"""List BindingRel definitions and references in tracked Lean source files."""
import json
import pathlib
import re
import subprocess

root = pathlib.Path(__file__).resolve().parents[4]
paths = subprocess.check_output(
    ["git", "ls-files", "--", "Solidity/**/*.lean"], cwd=root, text=True
).splitlines()
defs = []
references = []
for name in paths:
    for number, line in enumerate((root / name).read_text().splitlines(), 1):
        if not re.search(r"\bBindingRel\b", line):
            continue
        row = {"path": name, "line": number, "text": line.strip()}
        references.append(row)
        if re.search(r"\b(?:def|abbrev|theorem|lemma|inductive|structure)\s+BindingRel\b", line):
            defs.append(row)
print(json.dumps({"definitions": defs, "references": references}, indent=2))
