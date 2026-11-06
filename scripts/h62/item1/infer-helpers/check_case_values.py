#!/usr/bin/env python3
"""Check the candidate case table against a fixed external textual oracle.

This checks text only. It does not elaborate Lean or prove either inferencer.
"""
from pathlib import Path
import re
import sys
from lean_mask import mask

SPEC = Path("tests/h62/item1/infer-helpers/CaseSpecifications.lean")
# Each row pins the constructor arguments and (mapping, payable, location).
ROWS = {
    "int": ("_", "false", "false", ".memory"),
    "bool": ("", "false", "false", ".memory"),
    "address": ("_", "false", "true", ".memory"),
    "fixedBytes": ("_ _", "false", "false", ".memory"),
    "fixed": ("_", "false", "false", ".memory"),
    "enum": ("_", "false", "false", ".memory"),
    "udvt": ("_", "false", "false", ".memory"),
    "contract": ("_", "false", "true", ".memory"),
    "bytes": ("loc", "false", "false", "loc"),
    "string": ("loc", "false", "false", "loc"),
    "array": ("_ _ _", "false", "false", ".memory"),
    "struct": ("_ _", "false", "false", ".memory"),
    "mapping": ("_ _", "true", "false", ".memory"),
    "fn": ("_ _ _ _", "false", "false", ".memory"),
    "rational": ("_", "false", "false", ".memory"),
    "hexConst": ("_ _", "false", "false", ".memory"),
    "stringLit": ("_", "false", "false", ".memory"),
    "tuple": ("_", "false", "false", ".memory"),
}

def check(root):
    try:
        text = mask((root / SPEC).read_text(encoding="utf-8"))
        _, found, body = text.partition("def expected :")
        if not found:
            raise ValueError("missing expected definition")
        body, found, _ = body.partition("theorem source_cases")
        if not found:
            raise ValueError("missing expected definition terminator")
        signature, separator, arms_text = body.partition("\n")
        if not separator or " ".join(signature.split()) != "STy → Bool × Bool × DataLoc":
            raise ValueError("unexpected expected definition signature")
        seen = {}
        for line in arms_text.splitlines():
            if not line.strip():
                continue
            arm = re.fullmatch(r"\s*\|\s*\.([A-Za-z][A-Za-z0-9_]*)\b([^\n]*?)=>\s*\(([^\n]*)\)\s*", line)
            if arm is None:
                raise ValueError(f"unexpected case text: {line}")
            name, args, values = arm.groups()
            if name in seen:
                raise ValueError(f"duplicate case: {name}")
            parts = tuple(part.strip() for part in values.split(","))
            seen[name] = (" ".join(args.split()), *parts)
        if seen != ROWS:
            raise ValueError(f"case mismatch: observed={seen!r}")
    except (OSError, ValueError) as exc:
        print(exc, file=sys.stderr)
        return 1
    print(f"{len(ROWS)} case shapes and expected tuples match the textual oracle")
    return 0

if __name__ == "__main__":
    if len(sys.argv) > 2:
        sys.exit("usage: check_case_values.py [repository-root]")
    sys.exit(check(Path(sys.argv[1] if len(sys.argv) == 2 else ".")))
