#!/usr/bin/env python3
"""Pinned manual observations for unsigned division data and Source origins."""
import argparse, hashlib, json, pathlib, re, subprocess
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
PREFIX = "Solidity/Backend/PrimitivePackets/UnsignedDiv/"
OBS = {
 "Data.lean": {
  "Uint": "Alias for intrinsic unsigned integer values.",
  "sourceContext": "Source local context with two uint256 operands followed by arbitrary tail context.",
  "modelContext": "Intrinsic model local context with two uint operands followed by arbitrary tail context.",
  "sourceUInt": "Source uint256 value from an intrinsic unsigned value with a derived range witness.",
  "sourceLocals": "Source locals containing dividend then divisor followed by the supplied arbitrary local tail.",
  "sourceDiv": "Source division expression reading the first two uint256 locals.",
  "sourceMod": "Source remainder expression reading the first two uint256 locals.",
  "modelDiv": "Intrinsic model division expression reading the first two uint locals.",
  "modelMod": "Intrinsic model remainder expression reading the first two uint locals.",
 },
 "SourceOrigin.lean": {
  "source_div_origin": "For either pipeline, arbitrary frame and local tail, Source division evaluation at n+3 returns mapped uint256 intBin result and retains the complete local/state pair.",
  "source_mod_origin": "For either pipeline, arbitrary frame and local tail, Source remainder evaluation at n+3 returns mapped uint256 intBin result and retains the complete local/state pair.",
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
print(json.dumps({"method": "manual base-pinned literal headers; private lift_result is outside this census; not Lean checking or full case closure", "declarations": result}, indent=2))
