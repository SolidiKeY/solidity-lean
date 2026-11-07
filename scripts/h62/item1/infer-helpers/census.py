#!/usr/bin/env python3
"""Report the six named helper declarations and their locations.

This is a lexical census, not a Lean parser or a proof of equivalence.
Run from the repository root. Missing or duplicate definitions fail closed.
"""
import pathlib
import re
import sys
from lean_mask import mask

FILES = {
    "Solidity/Source/Infer.lean": ("STy.isMapping", "STy.isPayableArg", "STy.convLoc"),
    "Solidity/Frontend/Static/Infer.lean": ("isMappingTy", "payableArg", "convLoc"),
}

def census(root: pathlib.Path) -> int:
    failed = False
    for path, names in FILES.items():
        try:
            lines = mask((root / path).read_text(encoding="utf-8")).splitlines()
        except (OSError, ValueError) as exc:
            print(f"{path}: {exc}", file=sys.stderr)
            failed = True
            continue
        for name in names:
            definition = re.compile(r"^\s*(?:private\s+)?def\s+" + re.escape(name) + r"(?=\s|\(|:)")
            hits = [i for i, line in enumerate(lines, 1) if definition.search(line)]
            print(f"{path}: {name}: declaration lines {hits}")
            if len(hits) != 1:
                failed = True
    return int(failed)

if __name__ == "__main__":
    if len(sys.argv) > 2:
        sys.exit("usage: census.py [repository-root]")
    sys.exit(census(pathlib.Path(sys.argv[1] if len(sys.argv) == 2 else ".")))
