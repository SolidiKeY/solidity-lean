#!/usr/bin/env python3
"""Generate the additive imported-constant/type ledger fixture; bulk output stays off git."""
import json
from pathlib import Path
import sys
c=json.loads(Path(sys.argv[1]).read_text())
files=c["files"]
if len(sys.argv)>3:
    result=json.loads(Path(sys.argv[3]).read_text())
    passed={r["module"] for r in result["modules"] if r.get("exit")==0}
    files=[f for f in files if f["module"] in passed]
    if not files: raise SystemExit("no passing Source imports")
body="""
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some output ← liftIO (IO.getEnv "H62_API_OUTPUT")
    | throwError "H62_API_OUTPUT is required"
  let constants := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let rows := constants.filterMap fun (n, ci) => do
    let idx ← env.getModuleIdxFor? n
    let mod := env.header.moduleNames[idx.toNat]!
    if !mod.toString.startsWith "Solidity.Source." then none else
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
      some <| Json.mkObj [("module", toJson mod.toString), ("name", toJson n.toString),
        ("kind", toJson kind), ("universes", toJson (ci.levelParams.map Name.toString)),
        ("type_repr", toJson (reprStr ci.type))]
  let requested : List String := __SELECTED__
  let ledger := Json.mkObj [("schema", toJson (1 : Nat)), ("complete", Json.bool __COMPLETE__),
    ("assigned_module_count", toJson (__TOTAL__ : Nat)), ("requested_modules", toJson requested),
    ("rows", Json.arr rows), ("boundary", Json.str "Compiler-format observation; not semantic API equivalence")]
  liftIO <| IO.FS.writeFile output ledger.compress
  logInfo m!"H62 Source constant/type ledger: {rows.size} entries"
"""
body=body.replace("__SELECTED__",json.dumps([f["module"] for f in files])).replace("__TOTAL__",str(c["assigned_count"])).replace("__COMPLETE__",str(len(files)==c["assigned_count"]).lower())
Path(sys.argv[2]).write_text("import Lean\n"+"".join("import "+f["module"]+"\n" for f in files)+body)
