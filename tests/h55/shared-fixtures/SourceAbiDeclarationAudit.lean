import Lean
import Solidity.Lowering.V08.SourceAbiEntryControls

/-! Reflection-only baseline census; no production module imports this audit. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := #[`Solidity.Lowering.V08.SourceAbiControls,
    `Solidity.Lowering.V08.SourceAbiEntryControls]
  for modName in modules do
    let some idx := env.getModuleIdx? modName
      | throwError "module is not imported: {modName}"
    let names := (env.constants.toList.filterMap fun (name, _) =>
      if env.getModuleIdxFor? name == some idx then some name else none).mergeSort Name.quickLt
    for name in names do
      let some info := env.find? name | throwError "missing declaration: {name}"
      let axioms ← collectAxioms name
      let row := Json.mkObj [("module", toJson modName.toString), ("name", toJson name.toString),
        ("typeExpr", toJson (reprStr info.type)), ("levelParams", toJson (info.levelParams.map Name.toString)),
        ("axioms", toJson ((axioms.toList.mergeSort Name.quickLt).map Name.toString)),
        ("theorem", toJson info.isTheorem), ("unsafe", toJson info.isUnsafe),
        ("partial", toJson info.isPartial), ("axiom", toJson info.isAxiom)]
      IO.println ("H55_DECL " ++ row.compress)
