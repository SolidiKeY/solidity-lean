#!/usr/bin/env python3
"""Generate the additive imported-constant/type ledger fixture; bulk output stays off git."""
import json
from pathlib import Path
import sys
c=json.loads(Path(sys.argv[1]).read_text())
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
  liftIO <| IO.FS.writeFile output (Json.arr rows).compress
  logInfo m!"H62 Source constant/type ledger: {rows.size} entries"
"""
Path(sys.argv[2]).write_text("import Lean\n"+"".join("import "+f["module"]+"\n" for f in c["files"])+body)
