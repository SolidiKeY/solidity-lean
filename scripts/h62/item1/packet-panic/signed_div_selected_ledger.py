#!/usr/bin/env python3
"""Manual observations of pinned SignedDiv Selected declarations, not Lean proof."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FILE = "Solidity/Backend/PrimitivePackets/SignedDiv/Selected.lean"
OBS = {
    "minimum": "Intrinsic signed minimum literal.",
    "minusOne": "Intrinsic signed negative-one literal.",
    "raw": "Intrinsic division expression over two local operands.",
    "overflow": "Intrinsic boolean conjunction testing minimum dividend and negative-one divisor.",
    "expression": "Checked mode uses raw division; unchecked mode uses minimum for overflow and raw division otherwise.",
    "selectable": "The public memory compiler returns some compiled value for either checked mode and the given local indices.",
    "selected": "Compiled value extracted from public compiler result using the selectability witness.",
    "public_selection": "The public memory compiler returns the stated selected compiled value.",
    "raw_run": "With the stated target local reads, intrinsic raw evaluation is TRes.ofOpt of BinOp.div.evalT.",
    "overflow_run": "With the stated target local reads, intrinsic overflow predicate evaluates to the boolean decision for minimum dividend and negative-one divisor.",
    "expression_run": "With the stated target local reads, intrinsic expression evaluates as raw division in checked mode, minimumInt for unchecked minimum/-1, and raw division in other unchecked cases.",
    "runtime": "With the stated target local reads, physical StateRepr and arbitrary EVM-word tail, symbolic selected-code execution satisfies ValOutT for the stated checked/unchecked intrinsic result; no target panic payload is asserted.",
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
