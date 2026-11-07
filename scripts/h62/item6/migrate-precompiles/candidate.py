#!/usr/bin/env python3
"""Reproduce an OFF-GIT source snapshot of the exact authorized migration candidate.
No writes to producer originals; caller must choose a new output directory.
"""
import argparse,hashlib,importlib.util,json,subprocess
from contract import expected
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("census",HERE/"census.py");c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
ap=argparse.ArgumentParser();ap.add_argument("--out",type=Path,required=True);a=ap.parse_args()
root=Path.cwd(); census=c.census(root); assert census["migration_matches"]
out=a.out.resolve();out.mkdir(parents=True,exist_ok=False)
for m in census["topological_closure"]:
    rel=m.replace(".","/")+".lean";dest=out/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(expected(subprocess.check_output(["git","show",c.BASE+":"+rel],cwd=root),rel))
(out/".git").symlink_to((root/".git").resolve(),target_is_directory=True)
manifest={str(p.relative_to(out)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.rglob("*.lean"))}
(out/"source-sha256.json").write_text(json.dumps(manifest,indent=2)+"\n")
print(out)
