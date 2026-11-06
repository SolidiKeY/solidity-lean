#!/usr/bin/env python3
"""Textual snapshots of the six copied inference helpers.

Whitespace is ignored; this is not a Lean parser or equivalence proof. It
rejects comments or syntax changes inside the snapshots for manual review.
"""
from pathlib import Path
import re
import sys
from lean_mask import mask

EXPECTED = {
    "Solidity/Source/Infer.lean": {
        "STy.isMapping": "def STy.isMapping (τ : STy) : Bool := τ matches .mapping _ _",
        "STy.isPayableArg": "def STy.isPayableArg (σ : STy) : Bool := match σ with | .address _ => true | .contract _ => true | _ => false",
        "STy.convLoc": "def STy.convLoc (σ : STy) : DataLoc := match σ with | .bytes l => l | .string l => l | _ => .memory",
    },
    "Solidity/Frontend/Static/Infer.lean": {
        "isMappingTy": "def isMappingTy (τ : STy) : Bool := τ matches .mapping _ _",
        "payableArg": "def payableArg (σ : STy) : Bool := match σ with | .address _ => true | .contract _ => true | _ => false",
        "convLoc": "def convLoc (σ : STy) : DataLoc := match σ with | .bytes l => l | .string l => l | _ => .memory",
    },
}

def tokens(text):
    return re.findall(r"[^\W\d]\w*|\d+|:=|=>|[^\s]", text)

def check(root):
    errors = []
    for path, declarations in EXPECTED.items():
        try:
            text = (root / path).read_text(encoding="utf-8")
        except OSError as exc:
            errors.append(f"{path}: {exc}")
            continue
        try:
            active = mask(text)
        except ValueError as exc:
            errors.append(f"{path}: {exc}")
            continue
        for name, expected in declarations.items():
            pattern = r"(?m)^def\s+" + re.escape(name) + r"(?=\s|\(|:)"
            starts = list(re.finditer(pattern, active))
            if len(starts) != 1:
                errors.append(f"{path}: {name}: expected one declaration, found {len(starts)}")
                continue
            start = starts[0].start()
            end = re.search(r"(?m)^(?:def\s|/--|/-!)", text[starts[0].end():])
            stop = starts[0].end() + end.start() if end else len(text)
            if tokens(text[start:stop]) != tokens(expected):
                errors.append(f"{path}: {name}: shape changed")
            else:
                print(f"{path}: {name}: shape matches snapshot")
    for error in errors:
        print(error, file=sys.stderr)
    return int(bool(errors))

if __name__ == "__main__":
    if len(sys.argv) > 2:
        sys.exit("usage: check_shapes.py [repository-root]")
    sys.exit(check(Path(sys.argv[1] if len(sys.argv) == 2 else ".")))
