#!/usr/bin/env python3
"""Read-only lexical inventory of H55 fixture candidates; not an acceptance test."""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[3]
AREAS = ("Solidity/Lowering/V08", "Solidity/Backend/StorageOps", "Solidity/Lowering/StorageOps", "Solidity/Lowering/G19")
DECL = re.compile(r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev|theorem|lemma)\s+(\w+)")
NAMES = re.compile(r"^(?:extract_failure|fitting|uintSyntax|initial\w*|frame\w*)$")

for area in AREAS:
    for path in sorted((ROOT / area).glob("*Controls.lean")):
        for number, line in enumerate(path.read_text().splitlines(), 1):
            match = DECL.match(line)
            if match and NAMES.match(match.group(1)):
                print(f"{path.relative_to(ROOT)}:{number}:{match.group(1)}")
