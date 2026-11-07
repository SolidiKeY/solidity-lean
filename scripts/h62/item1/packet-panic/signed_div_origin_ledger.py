#!/usr/bin/env python3
"""Manual observations of pinned SignedDiv Origin declarations, not Lean proof."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FILE = "Solidity/Backend/PrimitivePackets/SignedDiv/Origin.lean"
OBS = {
    "T": "Signed 256-bit Source integer type.",
    "range": "Every intrinsic signed integer value lies within T's bounds.",
    "sourceValue": "Converts an intrinsic signed integer into a Source value using its proved range.",
    "locals_origin": "With the stated Source local reads and fuel+3, Source division evalE returns mapped binVal and retains the entire Source state for the original frame.",
    "source_zero": "For arbitrary checked flag and intrinsic operands whose divisor value is zero, Source binVal returns Source divZero panic.",
    "source_overflow": "For checked division of minimum signed value by -1, Source binVal returns arithmetic panic.",
    "source_unchecked_overflow": "For unchecked division of minimum signed value by -1, Source binVal succeeds with minimumInt.",
    "quotient_range": "For intrinsic operands with nonzero divisor excluding minimum/-1, the truncated quotient lies within T's bounds.",
    "quotient": "The truncated quotient represented as an intrinsic signed integer using nonzero and ordinary-case witnesses.",
    "source_ordinary": "For arbitrary checked flag, nonzero divisor and excluding minimum/-1, Source binVal succeeds with the represented truncated quotient.",
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
