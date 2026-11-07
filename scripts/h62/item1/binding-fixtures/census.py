#!/usr/bin/env python3
"""List BindingRel definitions and references in tracked Lean source files."""
import json
import pathlib
import re
import subprocess
from lexical import code_only, unknown_identifiers

root = pathlib.Path(__file__).resolve().parents[4]
paths = subprocess.check_output(
    ["git", "ls-files", "--", "Solidity/**/*.lean"], cwd=root, text=True
).splitlines()
defs = []
references = []
unknown = []
for name in paths:
    source=(root/name).read_text()
    if "BindingRel" not in source:continue
    unknown.extend({"path":name,**row} for row in unknown_identifiers(source))
    for number, line in enumerate(code_only(source).splitlines(), 1):
        if not re.search(r"\bBindingRel\b", line):
            continue
        row = {"path": name, "line": number, "text": line.strip()}
        references.append(row)
        if re.search(r"\b(?:def|abbrev|theorem|lemma|inductive|structure)\s+BindingRel\b", line):
            defs.append(row)
print(json.dumps({"definitions": defs, "references": references, "unknown_quoted_identifiers":unknown}, indent=2))
