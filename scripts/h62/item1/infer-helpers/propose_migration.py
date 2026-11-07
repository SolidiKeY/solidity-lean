#!/usr/bin/env python3
"""Emit a review-only patch; do not edit or register any production file.

The patch changes existing definition bodies and needs owner agreement,
Lean validation, registration and full gates before any adoption.
"""
from difflib import unified_diff
from pathlib import Path
import sys
from lean_mask import mask

ROOT = Path(__file__).resolve().parents[4]
SOURCE = "Solidity/Source/Infer.lean"
STATIC = "Solidity/Frontend/Static/Infer.lean"
NEW = "Solidity/Source/InferHelpers.lean"
SHARED = "Solidity.H62.InferHelpers.Shared"

REPLACEMENTS = {
    SOURCE: [
        ("def STy.isMapping (τ : STy) : Bool := τ matches .mapping _ _", f"def STy.isMapping (τ : STy) : Bool := {SHARED}.isMapping τ"),
        ("def STy.isPayableArg (σ : STy) : Bool :=\n  match σ with | .address _ => true | .contract _ => true | _ => false", f"def STy.isPayableArg (σ : STy) : Bool := {SHARED}.payableArg σ"),
        ("def STy.convLoc (σ : STy) : DataLoc :=\n  match σ with | .bytes l => l | .string l => l | _ => .memory", f"def STy.convLoc (σ : STy) : DataLoc := {SHARED}.convLoc σ"),
    ],
    STATIC: [
        ("def isMappingTy (τ : STy) : Bool := τ matches .mapping _ _", f"def isMappingTy (τ : STy) : Bool := {SHARED}.isMapping τ"),
        ("def payableArg (σ : STy) : Bool :=\n  match σ with\n  | .address _ => true\n  | .contract _ => true\n  | _ => false", f"def payableArg (σ : STy) : Bool := {SHARED}.payableArg σ"),
        ("def convLoc (σ : STy) : DataLoc :=\n  match σ with\n  | .bytes l => l\n  | .string l => l\n  | _ => .memory", f"def convLoc (σ : STy) : DataLoc := {SHARED}.convLoc σ"),
    ],
}

def emit(path, before, after, new=False):
    print(f"diff --git a/{path} b/{path}")
    if new: print("new file mode 100644")
    a = "/dev/null" if new else "a/" + path
    sys.stdout.writelines(unified_diff(before.splitlines(keepends=True), after.splitlines(keepends=True), fromfile=a, tofile="b/" + path))

def replace_live(text, old, new, path):
    if text.count(old) != 1:
        raise ValueError(f"anchor changed: {path}")
    offset = text.index(old)
    if mask(text)[offset:offset + len(old)] != old:
        raise ValueError(f"anchor is not live code: {path}")
    return text[:offset] + new + text[offset + len(old):]

def main():
    if (ROOT / NEW).exists():
        raise ValueError(f"destination exists: {NEW}")
    shared = (ROOT / "tests/h62/item1/infer-helpers/Shared.lean").read_text(encoding="utf-8")
    shared = "\n".join(line for line in shared.split("\n") if not line.startswith("#print axioms "))
    changes = []
    for path, pairs in REPLACEMENTS.items():
        before = (ROOT / path).read_text(encoding="utf-8")
        after = before
        anchor = "import Solidity.Source.Typing\n"
        after = replace_live(after, anchor, anchor + "import Solidity.Source.InferHelpers\n", path)
        for old, new in pairs:
            after = replace_live(after, old, new, path)
        changes.append((path, before, after))
    emit(NEW, "", shared, True)
    for path, before, after in changes: emit(path, before, after)

if __name__ == "__main__":
    try: main()
    except (OSError, ValueError) as exc: sys.exit(str(exc))
