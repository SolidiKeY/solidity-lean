#!/usr/bin/env python3
"""Manual observations of pinned SignedMod Source declarations, not Lean proof."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FILE = "Solidity/Backend/PrimitivePackets/SignedMod/Source.lean"
OBS = {
    "ty": "Signed 256-bit Source integer type.",
    "Range": "Inclusive lower and upper bounds of that type.",
    "lower": "Integer value built from x and its Range witness.",
    "remainder_range": "For arbitrary x and in-range nonzero y, x.tmod y is in Range.",
    "source_nonzero": "For arbitrary checked flag and in-range operands with nonzero divisor, Source binVal succeeds with x.tmod y.",
    "source_zero": "For arbitrary checked flag and in-range x and zero, Source binVal returns revert with Source divZero panic data.",
    "source_locals": "For the stated in-range local reads and fuel+3, Source evalE returns mapped binVal and retains the complete input state.",
    "source_locals_nonzero": "With the stated in-range local reads, fuel+3 and nonzero divisor, Source evalE returns x.tmod y and retains the complete input state.",
    "source_locals_zero": "With the stated in-range local reads, fuel+3 and zero divisor, Source evalE returns Source divZero panic data and retains the complete input state.",
    "negative_dividend": "For arbitrary integers, negating the dividend negates tmod.",
    "negative_divisor": "For arbitrary integers, negating the divisor preserves tmod.",
    "minimum_remainder_neg_one": "The minimum signed value tmod -1 equals zero; this is a pure integer equality.",
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
