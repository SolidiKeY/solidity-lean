import Solidity.Frontend.Testing

/-! Joined local preparation must retain positive proofs, leave false claims
pending, and preserve storage-writing proofs through the whole-leaf fallback. -/

open Lean Elab Command Tactic Meta Solidity

-- Successful whole-leaf macros must not mask the newer step handler.
run_elab do
  let env ← getEnv
  let kind := ``Solidity.tacticSol_spec_prep
  unless (Lean.Elab.macroAttribute.getEntries env kind).isEmpty do
    throwError "specification preparation unexpectedly has a masking macro"
  unless (tacticElabAttribute.getEntries env kind).head?.map (·.declName) ==
      some ``Solidity.evalSolSpecPrep do
    throwError "the joined preparation handler is not first"

solc_import "SimpPreparation.ast.json" hash 0xea285672c375200c as SimpPreparation testing
solc_scoped_problems SimpPreparation decl
#solkey_test SimpPreparation to ".lake/simp-preparation-results.json"

run_elab do
  let json ← match Json.parse (← IO.FS.readFile ".lake/simp-preparation-results.json") with
    | .ok json => pure json
    | .error message => throwError "invalid preparation results: {message}"
  let rows : Array Json ← Lean.ofExcept json.getArr?
  let expected := #[("maximum", "proved"), ("falseMaximum", "pending"),
    ("storeMaximum", "proved"), ("twoChoices", "proved"),
    ("constantOne", "proved"), ("falseConstant", "pending")]
  let actual ← rows.mapM fun (row : Json) => do
    let name ← Lean.ofExcept (row.getObjValAs? String "function")
    let status ← Lean.ofExcept (row.getObjValAs? String "status")
    pure (name, status)
  unless actual == expected do throwError "unexpected preparation results: {repr actual}"

-- Running preparation directly in a multi-goal state must retain siblings.
example : (Fml.Valid cspec[SimpPreparation]{ maximum }) ∧ True := by
  apply And.intro
  run_tac
    let [main, sibling] ← getGoals | throwError "expected two goals"
    let leaves ← CloseJ.runOn main (← `(tactic| sol_symex))
    setGoals (leaves ++ [sibling])
    let main := leaves.head!
    let before ← getGoals
    let target ← main.getType
    let failed ← tryCatchRuntimeEx (Budget.within 1 do
      evalTactic (← `(tactic| sol_close_join_prep))
      pure false) (fun _ => pure true)
    unless failed && (← getGoals) == before && !(← main.isAssigned) &&
        (← main.getType) == target do throwError "bounded preparation did not restore its goals"
    evalTactic (← `(tactic| sol_close_join_prep))
    unless (← getGoals).contains sibling do throwError "preparation dropped a sibling"
  all_goals first | trivial | sol_spec_finish
