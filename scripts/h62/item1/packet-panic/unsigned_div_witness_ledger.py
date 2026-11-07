#!/usr/bin/env python3
"""Manual observations of pinned UnsignedDiv Witness declarations, not Lean proof."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FILE = "Solidity/Backend/PrimitivePackets/UnsignedDiv/Witness.lean"
OBS = {
 "localState": "Intrinsic initial contract state with divisor then dividend pushed as uint locals.",
 "localWord": "Finite EVM word formed from the intrinsic unsigned value with a range witness.",
 "localMachine": "Auxiliary initial machine retaining supplied arbitrary saved stack, with operand words at memory cells 2 and 1 and zero elsewhere.",
 "localBases": "Constant zero finite-word base map.",
 "local_repr": "For arbitrary contract, unsigned operands and saved word stack, the stated initialized fragment and auxiliary machine satisfy the exact StateRepr parameters 1, 1 and 4.",
 "witnessed_division": "For nonzero divisor and arbitrary saved stack and Source local tail, Source fuel n+3 division succeeds with the .val truncated quotient retaining local/state pair, and the auxiliary selected symbolic machine pushes a represented result.",
 "witnessed_remainder": "For nonzero divisor and arbitrary saved stack and Source local tail, Source fuel n+3 remainder succeeds with the .val truncated remainder retaining local/state pair, and the auxiliary selected symbolic machine pushes a represented result.",
 "witnessed_zero_division": "For zero divisor and arbitrary saved stack and Source local tail, Source fuel n+3 returns exact divZero panic data retaining local/state pair, public selection holds, and the auxiliary selected symbolic machine coarsely reverts.",
}
p = argparse.ArgumentParser()
p.add_argument("--root", type=pathlib.Path, default=pathlib.Path.cwd())
p.add_argument("--declarations", type=pathlib.Path, required=True)
p.add_argument("--base-repository", type=pathlib.Path)
a = p.parse_args()
root = a.root.resolve()
rows = [r for r in json.loads(a.declarations.read_text())["declarations"] if r["file"] == FILE]
source = (root / FILE).read_bytes()
base = subprocess.check_output(["git", "show", BASE + ":" + FILE], cwd=a.base_repository or root)
digest = hashlib.sha256(source).hexdigest()
if source != base or any(r["sha256"] != digest for r in rows):
    p.error("source bytes differ from assigned base or census")
pattern = re.compile(r"^(theorem|lemma|def|abbrev)\s+([^\s(:]+)")
headers = [(i, m.group(1), m.group(2)) for i, line in enumerate(source.decode().splitlines(), 1) if (m := pattern.match(line))]
if [(r["line"], r["kind"], r["name"]) for r in rows] != headers:
    p.error("census headers differ from source")
names = [r["name"] for r in rows]
if len(set(names)) != len(names) or set(names) != set(OBS):
    p.error("observations do not exactly match source headers")
print(json.dumps({"method": "manual base-pinned textual observations; original premises remain binding; no Lean checking or full case closure", "declarations": [{**r, "observation": OBS[r["name"]]} for r in rows]}, indent=2))
