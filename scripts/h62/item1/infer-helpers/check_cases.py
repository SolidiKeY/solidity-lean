#!/usr/bin/env python3
"""Compare explicit case names with the current STy constructor inventory.

This lexical check does not check the expected values or Lean elaboration.
"""
from collections import Counter
from pathlib import Path
import re
import sys
from lean_mask import mask

SOURCE = Path("Solidity/Source/Types.lean")
SPEC = Path("tests/h62/item1/infer-helpers/CaseSpecifications.lean")

def cases(text, start, end, prefix):
    active = mask(text)
    before, sep, after = active.partition(start)
    if not sep:
        raise ValueError(f"missing section: {start}")
    body, sep, _ = after.partition(end)
    if not sep:
        raise ValueError(f"missing section terminator: {end}")
    return re.findall(r"(?m)^\s*\|\s*" + prefix + r"([A-Za-z][A-Za-z0-9_]*)\b", body)

def check(root):
    try:
        constructors = cases((root / SOURCE).read_text(), "inductive STy where", "deriving Repr", "")
        specified = cases((root / SPEC).read_text(), "def expected :", "theorem source_cases", r"\.")
    except (OSError, ValueError) as exc:
        print(exc, file=sys.stderr)
        return 1
    if not constructors or Counter(constructors) != Counter(specified) or any(n != 1 for n in Counter(specified).values()):
        print(f"constructor mismatch: source={constructors} specification={specified}", file=sys.stderr)
        return 1
    print(f"{len(constructors)} constructors specified exactly once: " + ", ".join(constructors))
    return 0

if __name__ == "__main__":
    if len(sys.argv) > 2:
        sys.exit("usage: check_cases.py [repository-root]")
    sys.exit(check(Path(sys.argv[1] if len(sys.argv) == 2 else ".")))
