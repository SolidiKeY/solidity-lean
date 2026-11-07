#!/usr/bin/env python3
"""List textual declaration headers in the packets covered by the case ledger."""
import argparse
import hashlib
import json
import pathlib
import re

parser = argparse.ArgumentParser()
parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path.cwd())
args = parser.parse_args()
root = args.root.resolve()
base = root / "Solidity/Backend/PrimitivePackets"
expected = {name: {"Source.lean", "Selected.lean", "Target.lean", "Agreement.lean", "Controls.lean"}
            for name in ("CheckedAdd", "CheckedSub", "CheckedMul", "SignedCheckedAdd",
                         "SignedCheckedSub", "SignedCheckedMul")}
expected["CheckedMul"].add("Populated.lean")
expected.update({
    "SignedDiv": {"Contract.lean", "Controls.lean", "Execution.lean", "Origin.lean", "Selected.lean"},
    "SignedMod": {"Controls.lean", "Selection.lean", "Source.lean"},
    "UnsignedDiv": {"Composition.lean", "Data.lean", "Execution.lean", "Numeric.lean", "Selection.lean", "SourceOrigin.lean", "Witness.lean"},
    "SignedSub": {"Controls.lean", "Execution.lean"},
})
pattern = re.compile(r"^(theorem|lemma|def|abbrev)\s+([^\s(:]+)")
rows = []
for family, names in sorted(expected.items()):
    directory = base / family
    actual = {p.name for p in directory.glob("*.lean")}
    if actual != names:
        parser.error(f"{family}: file set changed; expected {sorted(names)}, found {sorted(actual)}")
    for name in sorted(names):
        path = directory / name
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        for line_no, line in enumerate(data.decode("utf-8").splitlines(), 1):
            match = pattern.match(line)
            if match:
                rows.append({"file": path.relative_to(root).as_posix(), "sha256": digest,
                             "line": line_no, "kind": match.group(1), "name": match.group(2)})
print(json.dumps({"method": "literal line-start declaration headers; includes namespace-local declarations and is not Lean parsing or dependency closure", "declarations": rows}, ensure_ascii=False, indent=2))
