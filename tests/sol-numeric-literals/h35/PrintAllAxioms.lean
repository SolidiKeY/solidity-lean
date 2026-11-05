import Solidity.Frontend.NumericLiteralProofs.Audit

/-! H35 also prints every generated theorem constant, using its actual Name. -/
open Lean Elab Command

set_option pp.privateNames true in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let .thmInfo _ := info then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString.startsWith
            "Solidity.Frontend.NumericLiteralProofs." then
          names := names.push name
  if names.size != 808 then
    throwError "H35 theorem inventory drift: {names.size}"
  for name in names.qsort Name.lt do
    elabCommand (← `(command| #print axioms $(mkIdent name)))
