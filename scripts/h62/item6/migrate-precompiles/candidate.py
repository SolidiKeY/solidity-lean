#!/usr/bin/env python3
"""Reproduce an OFF-GIT source snapshot of the exact three-proof migration candidate.
No writes to producer originals; caller must choose a new output directory.
"""
import argparse,hashlib,importlib.util,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("census",HERE/"census.py");c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
ap=argparse.ArgumentParser();ap.add_argument("--out",type=Path,required=True);a=ap.parse_args()
root=Path.cwd(); census=c.census(root); assert census["source_frozen"]
out=a.out.resolve();out.mkdir(parents=True,exist_ok=False)
for m in census["topological_closure"]:
    rel=m.replace(".","/")+".lean";dest=out/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((root/rel).read_bytes())
(out/".git").symlink_to((root/".git").resolve(),target_is_directory=True)
p=out/"Solidity/Precompiles/Bls12381.lean";s=p.read_text()
for group in ("g1","g2"):
    old=f"theorem {group}Discount_length : {group}Discount.length = 128 := rfl"
    assert s.count(old)==1;s=s.replace(old,old[:-3]+"by decide +kernel")
p.write_text(s)
p=out/"Solidity/Precompiles/PointEval.lean";s=p.read_text()
old="| none => exact Option.noConfusion h"
assert s.count(old)==1;s=s.replace(old,"| none => cases h");p.write_text(s)
manifest={str(p.relative_to(out)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.rglob("*.lean"))}
(out/"source-sha256.json").write_text(json.dumps(manifest,indent=2)+"\n")
print(out)
