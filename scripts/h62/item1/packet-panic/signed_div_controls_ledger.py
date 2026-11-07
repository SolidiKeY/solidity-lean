#!/usr/bin/env python3
"""Manual observations of pinned SignedDiv Controls declarations, not Lean proof."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FILE = "Solidity/Backend/PrimitivePackets/SignedDiv/Controls.lean"
OBS = {
 "P": "Alias for the populated EVM fixture contract.",
 "Γ": "Target context with two signed locals followed by fixture context.",
 "F": "Initialized fixture fragment extended by two signed locals.",
 "target": "Fixture target state with intrinsic signed b then a pushed as locals.",
 "machine": "Fixture machine with signed b and a words written at cells 4 and 5.",
 "source": "Initial Source state with signed a and b local values and fixture state s0.",
 "word_repr": "The canonical signed word of any intrinsic signed value represents that value.",
 "word_unique": "A word representing the given intrinsic signed value equals its canonical signed word.",
 "initial": "For any intrinsic signed operands, fixture target and machine satisfy StateRepr 1 0 6.",
 "n": "Intrinsic signed integer formed from an integer and its inRange witness.",
 "negSeven": "Intrinsic signed fixture operand -7.",
 "two": "Intrinsic signed fixture operand 2.",
 "zero": "Intrinsic signed fixture operand 0.",
 "minus": "Intrinsic signed fixture operand -1.",
 "zero_both": "For either pipeline and checked flag, fuel+3 and arbitrary EVM-word tail, Source -7 divided by zero returns divZero panic data retaining Source state and selected symbolic code coarsely reverts.",
 "overflow_both": "For either pipeline, fuel+3 and arbitrary EVM-word tail, checked minimum/-1 returns Source arithmetic panic and coarse symbolic revert; unchecked returns Source minimum with state retained and symbolic success pushing its canonical word.",
 "truncation_both": "For either pipeline and checked flag, fuel+3 and arbitrary EVM-word tail, Source -7 divided by 2 returns -3 retaining Source state and selected symbolic code pushes signed -3.",
 "panic_classes_differ": "Source divZero panicData and arithmetic panicData are distinct.",
 "no_floor_rounding": "For either pipeline parameter and checked flag and arbitrary tail, selected symbolic -7/2 cannot return the stated -4 floor-rounded word.",
 "checked_not_wrap": "For either pipeline parameter and arbitrary tail, selected checked minimum/-1 cannot return the stated successful minimum-word push.",
 "capacity_witness": "Numeric stackBound checks at depth 4 hold for zeroTest, signedDivOverflowTest and SDIV body.",
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
