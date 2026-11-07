import Solidity.Automation.H28.Chain
import Solidity.Automation.H28.Prove
import Lean

/-! Every original syntax form and malformed argument controls.
These controls establish parser compatibility; owner proof/refusal tests remain
separate and require the original owner modules. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (input, expected) in [
      ("sol_h28_chain", ``Solidity.Automation.H28.tacticSolH28Chain),
      ("sol_h28_prove", ``Solidity.Automation.H28.tacticSolH28Prove),
      ("sol_h28_prove (steps := 0)", ``Solidity.Automation.H28.tacticSolH28Prove),
      ("sol_h28_prove (steps := 1)", ``Solidity.Automation.H28.tacticSolH28Prove)] do
    match Parser.runParserCategory env `tactic input with
    | .ok stx =>
      unless stx.getKind == expected do throwError "unexpected syntax kind for {input}"
      logInfo m!"SYNTAX_ACCEPT {input}"
    | .error message => throwError "syntax rejected {input}: {message}"
  for input in ["sol_h28_chain (steps := 1)", "sol_h28_prove (steps := -1)",
      "sol_h28_prove (steps := true)", "sol_h28_prove (steps :=)"] do
    match Parser.runParserCategory env `tactic input with
    | .ok _ => throwError "malformed syntax accepted: {input}"
    | .error _ => logInfo m!"SYNTAX_REJECT {input}"
