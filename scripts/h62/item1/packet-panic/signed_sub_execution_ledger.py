#!/usr/bin/env python3
"""Manual observations of pinned SignedSub Execution declarations, not Lean proof."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FILE = "Solidity/Backend/PrimitivePackets/SignedSub/Execution.lean"
OBS = {
 "ty": "Alias for the signed word subtraction Source type.",
 "value": "Intrinsic unchecked signed word subtraction value over two target locals.",
 "selected": "The compiled value extracted from the public memory compiler for the local subtraction expression.",
 "selection": "The public memory compiler returns the stated selected subtraction value.",
 "emitted_code": "The selected code loads both local cells, swaps operand order and subtracts.",
 "execution": "With the original IntegerLocalFamily, in-range operand and Source read premises and initial StateRepr, unchecked Source fuel+3 computes intWrap of x-y and retains Source state; for every EVM-word tail the selected symbolic run pushes the canonical wrapped signed word and retains the stated StateRepr.",
 "source_horizon_zero": "Unchecked Source subtraction at horizon zero returns timeout and retains the original Source state, independently of local-read premises.",
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
