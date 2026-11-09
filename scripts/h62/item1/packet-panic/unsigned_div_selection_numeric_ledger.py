#!/usr/bin/env python3
"""Pinned manual observations for unsigned division selection and numeric outcomes."""
import argparse, hashlib, json, pathlib, re, subprocess
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
PREFIX = "Solidity/Backend/PrimitivePackets/UnsignedDiv/"
OBS = {
 "Selection.lean": {
  "selectedDiv": "Constructed compiled uint division value with code and certificate for the two model locals.",
  "selectedMod": "Constructed compiled uint remainder value with code and certificate for the two model locals.",
  "select_div": "The public memory compiler returns the constructed selectedDiv value.",
  "select_mod": "The public memory compiler returns the constructed selectedMod value.",
  "div_code": "Selected division code is the two local memory loads followed by the uint division binTail.",
  "mod_code": "Selected remainder code is the two local memory loads followed by the uint remainder binTail.",
 },
 "Numeric.lean": {
  "div_result": "For a nonzero divisor, uint BinOp.div.evalT returns some intrinsic value whose .val equals the truncated quotient.",
  "mod_result": "For a nonzero divisor, uint BinOp.mod.evalT returns some intrinsic value whose .val equals the truncated remainder.",
  "source_div_result": "For either checked flag, nonzero divisor and supplied intrinsic v whose .val equals the truncated quotient, Source uint256 intBin division returns the Source representation of v.",
  "source_mod_result": "For either checked flag, nonzero divisor and supplied intrinsic v whose .val equals the truncated remainder, Source uint256 intBin remainder returns the Source representation of v.",
  "scalar_panic_bytes": "Scalar.divisionFailure equals Source divZero panicData; this states scalar-guard payload equality, not symbolic EVM revert payload correspondence.",
 },
}
p = argparse.ArgumentParser()
p.add_argument("--root", type=pathlib.Path, default=pathlib.Path.cwd())
p.add_argument("--declarations", type=pathlib.Path, required=True)
p.add_argument("--base-repository", type=pathlib.Path)
a = p.parse_args()
root = a.root.resolve()
census = json.loads(a.declarations.read_text())["declarations"]
result = []
pattern = re.compile(r"^(theorem|lemma|def|abbrev)\s+([^\s(:]+)")
for filename, descriptions in OBS.items():
    path = PREFIX + filename
    rows = [r for r in census if r["file"] == path]
    source = (root / path).read_bytes()
    base = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=a.base_repository or root)
    digest = hashlib.sha256(source).hexdigest()
    if source != base or any(r["sha256"] != digest for r in rows):
        p.error(path + ": source bytes differ from assigned base or census")
    headers = [(i, m.group(1), m.group(2)) for i, line in enumerate(source.decode().splitlines(), 1) if (m := pattern.match(line))]
    if [(r["line"], r["kind"], r["name"]) for r in rows] != headers:
        p.error(path + ": census headers differ from source")
    names = [r["name"] for r in rows]
    if len(set(names)) != len(names) or set(names) != set(descriptions):
        p.error(path + ": observations do not exactly match source headers")
    result.extend({**r, "observation": descriptions[r["name"]]} for r in rows)
print(json.dumps({"method": "manual base-pinned literal headers; private Numeric helpers are separately accounted; not Lean checking or full case closure", "declarations": result}, indent=2))
