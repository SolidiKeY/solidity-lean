#!/usr/bin/env python3
"""Manual observations of pinned SignedSub Controls declarations, not Lean proof."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FILE = "Solidity/Backend/PrimitivePackets/SignedSub/Controls.lean"
OBS = {
 (9,"C"): "Seed namespace alias for the structured-memory fixture contract.",
 (10,"initial"): "Seed namespace alias for the fixture initial intrinsic state.",
 (11,"machine"): "Seed namespace alias for the fixture machine.",
 (12,"bases"): "Seed namespace alias for the fixture base map.",
 (13,"represented"): "Seed namespace alias for the fixture initial representation.",
 (15,"C"): "Outer controls namespace alias for Seed.C.",
 (16,"Γ"): "Target context of two signed locals.",
 (17,"frag"): "Initialized fragment for the two-local context.",
 (18,"first"): "Target index for first signed local.",
 (19,"second"): "Target index for second signed local.",
 (21,"target"): "With signed range witnesses, Seed initial target extended by y then x locals.",
 (25,"machine"): "Seed machine with signed y and x words at cells 1 and 2.",
 (28,"represented"): "For in-range x and y, target and machine satisfy StateRepr 1 1 64 with the specified fragment and Seed bases.",
 (34,"source"): "Source state with range-witnessed signed x and y locals and s0.",
 (38,"si"): "Boolean-indexed mapping to the two Source local indices.",
 (42,"ti"): "Boolean-indexed mapping to the two target local indices.",
 (46,"family"): "For in-range x and y, Source locals and target environment form the stated IntegerLocalFamily.",
 (54,"application"): "The generic unchecked execution theorem instantiated with the fixture, arbitrary pipeline/fuel and range-witnessed x and y.",
 (60,"code"): "Selected subtraction code for the two target fixture locals.",
 (62,"public_selection"): "The public memory compiler returns the selected value for the fixture.",
 (65,"actual_code"): "Selected fixture code is mload 2, mload 1, swap 1, sub.",
 (67,"retained_run"): "For any pipeline, fuel, in-range x and y and arbitrary tail after w77,w88, selected symbolic code pushes the wrapped x-y word on that stack.",
 (74,"source_run"): "For any pipeline, fuel and in-range x and y, unchecked Source fuel+3 returns intWrap(x-y) and retains Source state.",
 (82,"signedResult"): "Projection from successful zero-cost EVM output with a value on top to its signed integer, otherwise none.",
 (86,"negative_left"): "The signedResult projection of fixture symbolic -5 minus 3 is -8.",
 (88,"negative_right"): "The signedResult projection of fixture symbolic 5 minus -3 is 8.",
 (90,"minimum"): "The minimum signed 256-bit integer constant.",
 (91,"maximum"): "The maximum signed 256-bit integer constant.",
 (93,"min_wrap"): "The signedResult projection of fixture symbolic minimum minus 1 is maximum.",
 (95,"max_wrap"): "The signedResult projection of fixture symbolic maximum minus -1 is minimum.",
 (97,"equal_operands"): "The signedResult projection of fixture symbolic minimum minus itself is zero.",
 (99,"wrong_sign_refused"): "The fixture symbolic -5 minus 3 signedResult is not positive 8.",
 (101,"unwrapped_result_refused"): "The fixture symbolic minimum minus 1 signedResult is not the unwrapped minimum-1.",
 (103,"both_source_pipelines"): "For either pipeline, unchecked Source horizon 3 projected result for minimum minus 1 is maximum.",
 (111,"source_negative_left"): "For either pipeline, unchecked Source horizon 3 projected result for -5 minus 3 is -8.",
 (119,"source_negative_right"): "For either pipeline, unchecked Source horizon 3 projected result for 5 minus -3 is 8.",
 (127,"both_source_max_wrap"): "For either pipeline, unchecked Source horizon 3 projected result for maximum minus -1 is minimum.",
 (135,"nonempty_frame"): "The initial fixture machine for -5 and 3 has stack [w77] and memory words w128 and w99 at 0 and 63.",
 (138,"no_horizon_promotion"): "For either pipeline, unchecked Source horizon zero on minimum minus 1 returns timeout retaining Source state.",
 (144,"checked_overflow_boundary"): "For either pipeline, checked Source horizon 3 minimum minus 1 has revertOf equal to some(Source arithmetic panicData).",
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
names = [(r["line"], r["name"]) for r in rows]
if len(set(names)) != len(names) or set(names) != set(OBS):
    p.error("observations do not exactly match source headers")
print(json.dumps({"method": "manual base-pinned textual observations; original premises remain binding; no Lean checking or full case closure", "declarations": [{**r, "observation": OBS[(r["line"], r["name"])]} for r in rows]}, indent=2))
