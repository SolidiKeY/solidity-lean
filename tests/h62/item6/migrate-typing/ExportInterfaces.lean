import Lean.Util.CollectAxioms
import Solidity.Typing.CanonTest
import Solidity.Typing.CleanTailRun
import Solidity.Typing.Sorts

/-! Read-only migration inventory, emitted off Git. Includes generated constants,
private declarations, exact elaborated Expr types, universe parameters and axioms.
This does not claim equality with an unbuilt new-toolchain environment. -/
open Lean in
run_cmd do
  let env ← getEnv
  let mut entries : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if moduleName.toString.startsWith "Solidity.Typing." then
        let axioms ← collectAxioms name
        entries := entries.push <| Json.mkObj [
          ("module", toJson moduleName.toString),
          ("name", toJson name.toString),
          ("levelParams", toJson (info.levelParams.map Name.toString)),
          ("typeExpr", toJson (reprStr info.type)),
          ("axioms", toJson ((axioms.toList.map Name.toString).mergeSort (· ≤ ·)))]
  let sortedEntries := entries.toList.mergeSort (fun a b =>
    (a.getObjValAs? String "name").toOption.getD "" ≤
    (b.getObjValAs? String "name").toOption.getD "")
  let some output ← IO.getEnv "TYPING_API_OUTPUT"
    | throwError "set TYPING_API_OUTPUT to an off-Git file"
  IO.FS.writeFile output ((toJson sortedEntries).pretty ++ "\n")
  logInfo m!"Exported {sortedEntries.length} Typing constants (types and axiom dependencies)"
