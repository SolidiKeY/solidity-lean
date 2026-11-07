#!/usr/bin/env python3
"""Emit an isolated Parser migration experiment, never edit production files.
Parser changes only the two diagnosed String operations; emitted Annotations
include the exact approved enum-tag compatibility additions. Sources stay off git.
"""
import argparse, difflib, hashlib, json, pathlib
import sys
sys.dont_write_bytecode = True
from census import ROOT
from migration import base_source, expected_sources
p=argparse.ArgumentParser(); p.add_argument("--out",required=True,type=pathlib.Path)
a=p.parse_args(); a.out.mkdir(parents=True) # refuse overwrite
rel="Solidity/SortCheck/Parser.lean"
old=base_source(rel)
assert old.splitlines().count("  let t := l.trim")==1
assert old.splitlines().count("    let n := (t.dropRight 1).trim")==1
new=old.replace("let t := l.trim", "let t := l.trimAscii.copy").replace("let n := (t.dropRight 1).trim", "let n := (t.dropEnd 1).trimAscii.copy")
target=a.out/rel; target.parent.mkdir(parents=True); target.write_text(new)
(a.out/"Solidity/SortCheck/Annotations.lean").write_text(expected_sources()["Solidity/SortCheck/Annotations.lean"])
(a.out/"ParserCases.lean").write_bytes((ROOT/"tests/h62/item6/migrate-sortcheck/ParserCases.lean").read_bytes())
(a.out/"SolkeyCheck.lean").write_bytes((ROOT/"SolkeyCheck.lean").read_bytes())
(a.out/"proposed-parser.patch").write_text("".join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile="a/"+rel,tofile="b/"+rel)))
manifest={str(x.relative_to(a.out)):hashlib.sha256(x.read_bytes()).hexdigest() for x in sorted(a.out.rglob("*")) if x.is_file()}
(a.out/"manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
print(json.dumps(manifest,indent=2))
