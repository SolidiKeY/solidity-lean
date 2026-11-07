#!/usr/bin/env python3
"""Manual observations of pinned SignedMod Controls declarations, not Lean proof."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FILE = "Solidity/Backend/PrimitivePackets/SignedMod/Controls.lean"
OBS = {
 "C": "Alias of the populated heap fixture contract.",
 "Γ": "Target context with two signed locals followed by fixture context.",
 "fragment": "Initialized fixture fragment extended by two signed locals.",
 "target": "Populated fixture target state extended with in-range y then x locals.",
 "machine": "Fixture machine with y and x signed words written at cells 4 and 5; range witnesses remain parameters.",
 "initial8": "The original populated heap fixture satisfies StateRepr with bounds 1, 0, 8.",
 "initial": "For in-range x and y the extended target and machine satisfy StateRepr 1 0 8.",
 "E": "Source environment with empty layout.",
 "program": "Fixture Source program with absent bodies, constants and constructors and empty contract data.",
 "fixed": "Fixture Roadmap fixed functions and bounds; not general cryptographic or external-call agreement.",
 "globals": "Source globals from the given pipeline and fixed fixture functions.",
 "frame": "Source frame parameterized by checked flag with fixed sender and contract fields.",
 "source": "Initial Source state with in-range x and y signed locals and initialized storage state.",
 "code": "Publicly selected signed remainder code for the two fixture locals.",
 "target_success": "For in-range operands and nonzero divisor, selected symbolic execution on w77 followed by arbitrary tail succeeds with the represented truncated remainder above w77 and the original other machine fields.",
 "target_failure": "For in-range x and zero divisor, selected symbolic execution on w77 followed by arbitrary tail returns coarse revert.",
 "source_success": "For either pipeline and checked flag, in-range operands, nonzero divisor and fuel+3, Source returns x.tmod y retaining the complete Source state.",
 "source_failure": "For either pipeline and checked flag, in-range x, zero divisor and fuel+3, Source returns divZero panic data retaining complete Source state.",
 "raw_zero_differs": "For numeric input [7,0,77], raw SMOD yields [0,77] whereas the zero-guarded numeric component yields divisionFailure.",
 "nonempty_tail": "The singleton saved stack [w77] is nonempty.",
 "ordinary": "Selected symbolic 7 mod 3 succeeds with word 1 above w77 and arbitrary tail.",
 "negative": "Selected symbolic -7 mod 3 succeeds with signed word -1 above w77 and arbitrary tail.",
 "minimum": "Selected symbolic minimum signed value mod -1 succeeds with word 0 above w77 and arbitrary tail.",
 "negative_divisor_run": "Selected symbolic 7 mod -3 succeeds with word 1 above w77 and arbitrary tail.",
 "both_negative": "Selected symbolic -7 mod -3 succeeds with signed word -1 above w77 and arbitrary tail.",
 "too_short_horizon": "For either pipeline and checked flag, Source 7 mod 3 at horizon zero times out and retains Source state.",
 "horizon_two_timeout": "For either pipeline and checked flag, Source 7 mod 3 at horizon two times out and retains Source state.",
 "corrupted_saved_tail": "For any tail, selected symbolic 7 mod 3 cannot return the stated result with saved w77 changed to w88.",
 "short_frame_refused": "For in-range x and y the stated fixture cannot satisfy StateRepr with frame bound 5.",
 "observed_heap": "For in-range x and y, the initial fixture machine has the stated concrete words in the five specified memory cells.",
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
