#!/usr/bin/env python3
"""Generate a read-only environment census; canonicalize closed type expressions."""
import argparse,json,hashlib
from pathlib import Path
from census import inventory
LEAN = r'''
open Lean Elab Command
private partial def lc : Level → String
  | .zero => "z"
  | .succ a => "s(" ++ lc a ++ ")"
  | .max a b => "max(" ++ lc a ++ "," ++ lc b ++ ")"
  | .imax a b => "imax(" ++ lc a ++ "," ++ lc b ++ ")"
  | .param n => "param(" ++ n.toString ++ ")"
  | .mvar _ => "MVAR"
private def bc : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"
private partial def ec : Expr → String
  | .bvar n => "b" ++ toString n
  | .fvar _ => "FVAR"
  | .mvar _ => "MVAR"
  | .sort u => "sort(" ++ lc u ++ ")"
  | .const n us => "const(" ++ n.toString ++ ";" ++ String.intercalate "," (us.map lc) ++ ")"
  | .app (.app (.const ``autoParam _) type) _ => ec type
  | .app f a => "app(" ++ ec f ++ "," ++ ec a ++ ")"
  | .lam _ t b bi => "lam(" ++ bc bi ++ "," ++ ec t ++ "," ++ ec b ++ ")"
  | .forallE _ t b bi => "forall(" ++ bc bi ++ "," ++ ec t ++ "," ++ ec b ++ ")"
  | .letE _ t v b _ => "let(" ++ ec t ++ "," ++ ec v ++ "," ++ ec b ++ ")"
  | .lit l => "lit(" ++ reprStr l ++ ")"
  | .mdata _ b => ec b
  | .proj n i b => "proj(" ++ n.toString ++ "," ++ toString i ++ "," ++ ec b ++ ")"
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.header.moduleNames[idx.toNat]!
      if mod.toString.startsWith "Solidity.Syntax." then
        let axs ← collectAxioms n
        rows := rows.push (Json.mkObj [("name", Json.str n.toString), ("module", Json.str mod.toString),
          ("type", Json.str (ec ci.type)), ("universes", toJson (ci.levelParams.map Name.toString)), ("axioms", toJson (axs.toList.map Name.toString))])
  let some output ← liftIO (IO.getEnv "SYNTAX_API_OUTPUT") | throwError "SYNTAX_API_OUTPUT required"
  liftIO (IO.FS.writeFile output (Json.arr rows).compress)
'''
if __name__=="__main__":
 p=argparse.ArgumentParser();p.add_argument("--modules",nargs="*");p.add_argument("--root",type=Path,default=Path.cwd());p.add_argument("--generate",type=Path);p.add_argument("--canonicalize",type=Path);p.add_argument("--output",type=Path);a=p.parse_args()
 if a.generate:
  text="import Lean\n"+"".join("import "+r["module"]+"\n" for r in inventory(a.root)["files"] if not a.modules or r["module"] in a.modules)+LEAN
  a.generate.write_text(text)
 if a.canonicalize:
  rows=json.loads(a.canonicalize.read_text());rows.sort(key=lambda r:(r["module"],r["name"]))
  assert len({r["name"] for r in rows})==len(rows)
  assert not any("MVAR" in r["type"] or "FVAR" in r["type"] for r in rows)
  a.output.write_text(json.dumps(rows,indent=2,sort_keys=True)+"\n")
  print(json.dumps(dict(constants=len(rows),sha256=hashlib.sha256(a.output.read_bytes()).hexdigest())))
