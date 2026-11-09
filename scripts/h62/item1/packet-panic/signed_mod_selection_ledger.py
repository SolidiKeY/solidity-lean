#!/usr/bin/env python3
"""Manual observations of pinned SignedMod Selection declarations, not Lean proof."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FILE = "Solidity/Backend/PrimitivePackets/SignedMod/Selection.lean"
OBS = {
    "expression": "Intrinsic signed remainder of two local operands.",
    "selected": "Selected compiled value contains binary signed remainder code with both local memory loads and its certificate.",
    "public_selection": "The public memory compiler returns the selected value for the given context and locals.",
    "target_nonzero": "For in-range x and y with y nonzero, intrinsic BinOp.mod.evalT operator evaluation returns the lowered x.tmod y.",
    "target_zero": "For in-range x and zero, intrinsic BinOp.mod.evalT operator evaluation returns none.",
    "int_repr_unique": "Two EVM words representing the same intrinsic signed integer value are equal.",
    "selected_remainder": "With the original Source and target reads, ranges, physical StateRepr, saved List (Fin Evm.W) converted to machine/numeric words and both numeric stack-capacity premises, establishes public selection, Source local evaluation with fuel+3 and retained state, symbolic value-out, and guarded numeric SMOD remainder outcome using divisionOutcome.",
    "selected_success": "With in-range operands, nonzero divisor, target reads and physical StateRepr, selected symbolic code on an arbitrary tail returns a represented remainder pushed onto that tail with the stated machine fields preserved; no numeric capacity assertion.",
    "selected_zero": "With in-range x and zero, target reads and physical StateRepr, selected symbolic code on an arbitrary tail returns coarse revert; no target panic payload is stated.",
    "origin_success": "With original Source and target reads, ranges, nonzero divisor and physical StateRepr, public selection, Source fuel+3 success with retained state, and symbolic target success with represented remainder on arbitrary tail hold.",
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
