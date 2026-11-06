#!/usr/bin/env python3
"""Generate an unvalidated owner-applied patch against the reviewed base file."""
import difflib
import hashlib
import pathlib
import sys

root = pathlib.Path(__file__).resolve().parents[4]
relative = "Solidity/Backend/PrimitivePackets/CheckedMul/Controls.lean"
original = (root / relative).read_bytes()
if hashlib.sha256(original).hexdigest() != "1ed6c50483da571ca9ab70e85c5e71900fe112a7a05e24ef359899bdc49a56a8":
    raise SystemExit("CheckedMul Controls differs from reviewed base")
before = original.decode("utf-8")
after = before.replace("import Solidity.Backend.PrimitivePackets.CheckedMul.Agreement\n",
                       "import Solidity.Backend.PrimitivePackets.CheckedMul.Agreement\nimport Solidity.Backend.PrimitivePackets.PanicBytes\n", 1)
statements = {
    "exact_panic_bytes": "Source.panicData .arithmetic =\n    [0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x11]",
    "panic_not_truncated": "Source.panicData .arithmetic ≠\n    [0x4e,0x48,0x7b,0x71,0x11]",
    "panic_not_empty": "Source.panicData .arithmetic ≠ []",
}
for name, statement in statements.items():
    old = f"theorem {name} : {statement} := by\n  first | decide | rfl | omega"
    new = f"theorem {name} : {statement} := by\n  exact Solidity.Backend.PrimitivePackets.PanicBytes.{name}"
    if after.count(old) != 1:
        raise SystemExit(f"expected exactly one original proof for {name}")
    after = after.replace(old, new, 1)
if after == before or after.count("import Solidity.Backend.PrimitivePackets.PanicBytes\n") != 1:
    raise SystemExit("failed to construct unique helper import")
sys.stdout.writelines(difflib.unified_diff(before.splitlines(keepends=True), after.splitlines(keepends=True),
                                         fromfile="a/" + relative, tofile="b/" + relative))
