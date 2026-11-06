#!/usr/bin/env python3
"""Generate a read-only Lean probe for corpus-owned elaborated constant types.
Raw Expr representations are evidence; differences require review, not automatic
claims of changed semantics. This tool does not register a module or alter proofs.
"""
import pathlib,sys
path=pathlib.Path(sys.argv[1])
path.write_text("""import Lean
import Solidity.Corpus.Basic
import Solidity.Corpus.Imported
import Solidity.Corpus.TestSuite
import Solidity.Corpus.SolcExpressions
import Solidity.Corpus.SolcStructs
import Solidity.Corpus.SolcArrays
import Solidity.Corpus.SolcMemory
import Solidity.Corpus.SolcMappings
import Solidity.Corpus.SolcControlFlow

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array (String × Json) := #[]
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if "Solidity.Corpus.".isPrefixOf moduleName.toString then
        let row := Json.mkObj [
          ("name", toJson n.toString),
          ("module", toJson moduleName.toString),
          ("levels", toJson (ci.levelParams.map Name.toString)),
          ("typeExpr", toJson (reprStr ci.type))]
        rows := rows.push (n.toString, row)
  let sorted := rows.qsort (fun a b => decide (a.1 < b.1))
  let some output ← IO.getEnv "H62_INTERFACE_OUTPUT"
    | throwError "H62_INTERFACE_OUTPUT is required"
  let lines := sorted.toList.map (fun row => row.2.compress)
  IO.FS.writeFile output (String.intercalate "\\n" lines ++ "\\n")
""")
