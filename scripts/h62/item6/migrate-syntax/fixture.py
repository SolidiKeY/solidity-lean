#!/usr/bin/env python3
"""Emit a non-production, reproducible shadow fixture; never edits owned originals."""
import argparse, difflib, hashlib, json, subprocess
from pathlib import Path
from census import inventory
REPLACEMENTS = {
 "Solidity/Syntax/Grammar.lean": [
  ("(s[1].getAtomVal.dropRight 1)", "((s[1].getAtomVal.dropEnd 1).copy)"),
  ("(sym.dropRight 1)", "((sym.dropEnd 1).copy)"),
  ("(r[1].getAtomVal.dropRight 1)", "((r[1].getAtomVal.dropEnd 1).copy)"),
 ],
 "Solidity/Syntax/Raw.lean": [
  ("HashKind.ofName? (f.drop 1)", "HashKind.ofName? ((f.drop 1).copy)"),
  ("(s.drop 9).toList", "s.toList.drop 9"),
  ("if ext then rest.drop 8 else rest", "if ext then (rest.drop 8).copy else rest"),
  ("splitTopCommas ((rest.drop 8).dropRight 1)", "splitTopCommas (((rest.drop 8).dropEnd 1).copy)"),
  (".find? c.endsWith", ".find? (fun suffix => c.endsWith suffix)"),
  ("PrimTy.ofName? (c.dropRight loc.length)", "PrimTy.ofName? ((c.dropEnd loc.length).copy)"),
  ("String.mk", "String.ofList"),
 ],
}
def generate(root, output, from_base=False):
 if output.exists(): raise ValueError("Refusing existing fixture directory")
 inv=inventory(root); output.mkdir(parents=True); changes=[]; patch=[]
 for mod in inv["build_order"]:
  rel=Path(mod.replace(".","/")+".lean"); source=(subprocess.check_output(["git","show","c6f550e281a7e5affa9a99bc2cdaed556dec00e4:"+str(rel)],cwd=root).decode() if from_base else (root/rel).read_text()); target=source
  for old,new in REPLACEMENTS.get(str(rel),[]):
   if old in target: target=target.replace(old,new)
   elif new not in target: raise ValueError("Replacement no longer applies: "+old)
  p=output/rel; p.parent.mkdir(parents=True,exist_ok=True); p.write_text(target)
  if source!=target:
   changes.append(dict(path=str(rel),base_sha256=hashlib.sha256(source.encode()).hexdigest(),fixture_sha256=hashlib.sha256(target.encode()).hexdigest()))
   patch.extend(difflib.unified_diff(source.splitlines(True),target.splitlines(True),fromfile="a/"+str(rel),tofile="b/"+str(rel)))
 (output/"candidate.patch").write_text("".join(patch))
 (output/"fixture.json").write_text(json.dumps(dict(status="UNAPPROVED-FIXTURE-ONLY",changes=changes),indent=2)+"\n")
if __name__=="__main__":
 p=argparse.ArgumentParser(); p.add_argument("--from-base",action="store_true"); p.add_argument("--root",type=Path,default=Path.cwd()); p.add_argument("--output",type=Path,required=True); a=p.parse_args(); generate(a.root,a.output,a.from_base)
