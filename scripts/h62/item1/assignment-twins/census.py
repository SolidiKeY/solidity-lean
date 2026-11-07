#!/usr/bin/env python3
"""List declarations and branch labels in the six frozen assignment files."""
import hashlib
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[4]
DIRECTORY = ROOT / "Solidity/Backend/Passes"
DECL = re.compile(r"^\s*(?:@\[[^]]+\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(def|abbrev|theorem|lemma|example|structure|inductive)\s+([^\s:{(]+)")
CASE = re.compile(r"^\s*\|\s*\.?(legacy|viaIR)\s*=>")
for operation in ("Addition", "Multiplication", "Subtraction"):
    for kind in ("Pass", "Controls"):
        path = DIRECTORY / f"Assignment{operation}{kind}.lean"
        raw = path.read_bytes()
        print(f"{path.relative_to(ROOT)} sha256={hashlib.sha256(raw).hexdigest()}")
        for line, text in enumerate(raw.decode().splitlines(), 1):
            match = DECL.match(text)
            if match:
                print(f"  {line}: {match.group(1)} {match.group(2)}")
            match = CASE.match(text)
            if match:
                print(f"  {line}: branch {match.group(1)}")
