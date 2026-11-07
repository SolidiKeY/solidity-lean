#!/usr/bin/env python3
"""Additional literal private/protected headers in the pinned 48-file census."""
import argparse, hashlib, json, pathlib, re, subprocess
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
PREFIX = "Solidity/Backend/PrimitivePackets/"
EXPECTED = {name: {"Source.lean", "Selected.lean", "Target.lean", "Agreement.lean", "Controls.lean"}
            for name in ("CheckedAdd", "CheckedSub", "CheckedMul", "SignedCheckedAdd", "SignedCheckedSub", "SignedCheckedMul")}
EXPECTED["CheckedMul"].add("Populated.lean")
EXPECTED.update({
 "SignedDiv": {"Contract.lean", "Controls.lean", "Execution.lean", "Origin.lean", "Selected.lean"},
 "SignedMod": {"Controls.lean", "Selection.lean", "Source.lean"},
 "UnsignedDiv": {"Composition.lean", "Data.lean", "Execution.lean", "Numeric.lean", "Selection.lean", "SourceOrigin.lean", "Witness.lean"},
 "SignedSub": {"Controls.lean", "Execution.lean"},
})
EXPECTED_FILES = {PREFIX + family + "/" + name for family, names in EXPECTED.items() for name in names}
OBS = {
 ("CheckedMul/Populated.lean", "ref_cases"): "Any primitive-array reference in fixture heap H has uint element type and is heterogeneously equal to r0 or r1.",
 ("CheckedMul/Populated.lean", "noStructs"): "There is no struct reference in fixture heap H.",
 ("SignedSub/Execution.lean", "int_word_unique"): "Two machine words representing the same intrinsic signed integer value are equal.",
 ("UnsignedDiv/Execution.lean", "successful_word"): "A successful uint ValOutT observation entails a represented word and the stated machine push outcome.",
 ("UnsignedDiv/Execution.lean", "refused_word"): "A uint ValOutT observation for intrinsic revert entails coarse EVM revert.",
 ("UnsignedDiv/Numeric.lean", "value_of_some"): "If unsigned ofInt? returns some v, v.val equals its input integer.",
 ("UnsignedDiv/Numeric.lean", "source_int_result"): "For any checked flag, Source intRes of an intrinsic uint value returns its Source representation.",
 ("UnsignedDiv/SourceOrigin.lean", "lift_result"): "Lifting any uint256 Source result and mapping it to RVal preserves the supplied local/state pair.",
 ("UnsignedDiv/Witness.lean", "local_word_repr"): "The locally constructed finite word represents the original intrinsic uint value.",
}
p = argparse.ArgumentParser()
p.add_argument("--root", type=pathlib.Path, default=pathlib.Path.cwd())
p.add_argument("--base-repository", type=pathlib.Path)
p.add_argument("--declarations", type=pathlib.Path, required=True)
a = p.parse_args()
root = a.root.resolve()
census = json.loads(a.declarations.read_text())["declarations"]
files = sorted({r["file"] for r in census})
if set(files) != EXPECTED_FILES:
    p.error("expected the original 48 packet files")
pat = re.compile(r"^\s*(private|protected)\s+(theorem|lemma|def|abbrev)\s+([^\s(:]+)")
rows = []
for name in files:
    data = (root / name).read_bytes()
    base = subprocess.check_output(["git", "show", BASE + ":" + name], cwd=a.base_repository or root)
    digest = hashlib.sha256(data).hexdigest()
    if data != base or any(r["sha256"] != digest for r in census if r["file"] == name):
        p.error(name + ": source bytes differ from assigned base or census")
    for number, line in enumerate(data.decode().splitlines(), 1):
        if m := pat.match(line):
            key = (name.removeprefix(PREFIX), m.group(3))
            if key not in OBS:
                p.error("unaccounted literal header " + repr(key))
            rows.append({"file": name, "sha256": digest, "line": number, "modifier": m.group(1), "kind": m.group(2), "name": m.group(3), "observation": OBS[key]})
keys = [(r["file"].removeprefix(PREFIX), r["name"]) for r in rows]
if len(keys) != len(set(keys)) or set(keys) != set(OBS):
    p.error("missing or duplicate pinned private/protected headers")
print(json.dumps({"method": "literal private/protected headers in original 48 files, pinned base bytes; not Lean parsing or full semantic closure", "declarations": rows}, indent=2))
