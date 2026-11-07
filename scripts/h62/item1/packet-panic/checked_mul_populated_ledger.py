#!/usr/bin/env python3
"""Manual observations of pinned CheckedMul Populated declarations, not Lean proof."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FILE = "Solidity/Backend/PrimitivePackets/CheckedMul/Populated.lean"
OBS = {
 "C": "Empty fixture contract.",
 "H": "Fixture heap type containing two uint primitive arrays.",
 "r0": "Reference to the first uint array in H.",
 "r1": "Reference to the second uint array in H.",
 "base": "Finite-word base map choosing 16 for id 0 and 20 otherwise.",
 "uint": "Intrinsic uint value constructed from a natural and proof it is below W.",
 "hp": "Fixture heap containing uint arrays [7,9] and [4].",
 "Γ": "Context with a uint value and three uint array memory references.",
 "σ": "Initial contract storage and populated heap with uint 0, two aliases to r0 and one reference to r1.",
 "machine": "Initialized machine with concrete local pointers and array length/element words at specified addresses, zero elsewhere.",
 "array0_repr": "The populated fixture machine represents array r0 at base 0 (address 16).",
 "array1_repr": "The populated fixture machine represents array r1 at base 1 (address 20).",
 "heap_repr": "The fixture machine satisfies HeapRepr hp base 4.",
 "fixture_repr": "The fixture state and machine satisfy StateRepr 1 0 4 for the initialized context fragment.",
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
