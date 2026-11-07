#!/usr/bin/env python3
"""Pinned manual observations for unsigned division execution and composition."""
import argparse, hashlib, json, pathlib, re, subprocess
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
PREFIX = "Solidity/Backend/PrimitivePackets/UnsignedDiv/"
OBS = {
 "Execution.lean": {
  "div_eval": "Intrinsic model division evaluation equals TRes.ofOpt of uint division on the two environment operands.",
  "mod_eval": "Intrinsic model remainder evaluation equals TRes.ofOpt of uint remainder on the two environment operands.",
  "selected_div_execution": "With initial StateRepr and nonzero divisor, public selection and selected symbolic execution succeed with a represented truncated quotient pushed onto the original machine.",
  "selected_mod_execution": "With initial StateRepr and nonzero divisor, public selection and selected symbolic execution succeed with a represented truncated remainder pushed onto the original machine.",
  "selected_div_zero": "With initial StateRepr and zero divisor, public selection holds and selected symbolic division coarsely reverts.",
  "selected_mod_zero": "With initial StateRepr and zero divisor, public selection holds and selected symbolic remainder coarsely reverts.",
 },
 "Composition.lean": {
  "division_packet": "With initial StateRepr and nonzero divisor, public selection, Source fuel n+3 division with original local/state pair retained, and selected symbolic success with represented truncated quotient all hold for the common intrinsic operands.",
  "remainder_packet": "With initial StateRepr and nonzero divisor, public selection, Source fuel n+3 remainder with original local/state pair retained, and selected symbolic success with represented truncated remainder all hold for the common intrinsic operands.",
  "division_zero_packet": "With initial StateRepr and zero divisor, Source fuel n+3 division returns exact divZero panic data retaining the local/state pair, public selection holds, and selected symbolic code coarsely reverts.",
  "remainder_zero_packet": "With initial StateRepr and zero divisor, Source fuel n+3 remainder returns exact divZero panic data retaining the local/state pair, public selection holds, and selected symbolic code coarsely reverts.",
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
print(json.dumps({"method": "manual base-pinned literal headers; private execution helpers are separately accounted; not Lean checking or full case closure", "declarations": result}, indent=2))
