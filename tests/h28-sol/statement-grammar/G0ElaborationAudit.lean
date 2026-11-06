import Lean
import Solidity.Frontend.StatementGrammarH28.FixtureData
import Solidity.Frontend.StatementGrammarH28.G0Nodes
import Solidity.Frontend.StatementGrammarH28.G0Rejections
import Solidity.Frontend.StatementGrammarH28.BlockLeafCoverage
import Solidity.Frontend.StatementGrammarH28.FramedItemList

/-! Elaboration-time evidence only: record the actual generalized eliminators.
This does not prove object-language correctness or change any scanner policy. -/
open Lean Elab Command

set_option pp.explicit true in
run_cmd do
  let targets := ["rootAt", "listCellAt", "listValuesAt", "listLengthAt",
    "optionalBodyCtorsAt", "functionBodyCtorsAt", "topBodyCtorsAt",
    "fixtureBodyCtorsAt", "framedItemAt", "rootResult", "listCellResult",
    "listValuesResult", "framedItemResult", "nodeCtorsAt", "optValueAt", "optValueResult",
    "identAt", "litAt", "placeholdersAt", "nodesAt", "listViewResult", "listViewAt",
    "yulExprStmtAt", "yulCallAt", "yulPathAt", "yulLitAt"]
  let declarations := (← getEnv).constants.fold (init := #[]) fun acc name info =>
    if "_private.Solidity.Frontend.StatementGrammarH28.".isPrefixOf name.toString &&
        targets.any (fun suffix => name.toString.endsWith ("." ++ suffix)) then
      acc.push (name, info)
    else acc
  unless declarations.size == targets.length do
    throwError "G0 observer inventory mismatch: {declarations.size} vs {targets.length}"
  for (name, info) in declarations do
    let some value := info.value? | throwError "G0 observer has no body: {name}"
    logInfo m!"G0-ELAB {name}
TYPE {info.type}
VALUE {value}"
