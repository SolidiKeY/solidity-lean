#!/usr/bin/env python3
"""Manual observations of pinned SignedDiv Execution declarations, not Lean proof."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FILE = "Solidity/Backend/PrimitivePackets/SignedDiv/Execution.lean"
OBS = {
    "intrinsic_ordinary": "For intrinsic operands with a nonzero divisor excluding minimum/-1, BinOp.div.evalT returns the represented truncated quotient.",
    "intrinsic_zero": "With the stated target local reads and zero divisor, the intrinsic expression returns revert in either checked mode.",
    "intrinsic_overflow": "With target local reads and the minimum/-1 operands, intrinsic checked evaluation returns revert and unchecked evaluation returns minimumInt.",
    "ordinary_execution": "For either Source checked flag, with Source and target local reads, nonzero divisor, minimum/-1 excluded, physical StateRepr and arbitrary EVM-word tail, Source fuel+3 succeeds with retained state and selected symbolic execution pushes a represented quotient onto the tail.",
    "zero_execution": "For either Source checked flag, with Source and target local reads, zero divisor, physical StateRepr and arbitrary EVM-word tail, Source fuel+3 returns divZero panic data with retained state and selected symbolic execution returns coarse revert.",
    "overflow_execution": "With Source and target local reads, minimum/-1 operands, physical StateRepr and arbitrary EVM-word tail, checked Source fuel+3 returns arithmetic panic data with retained state and selected code coarsely reverts; unchecked Source succeeds with minimumInt and retained state and selected code pushes its represented value.",
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
