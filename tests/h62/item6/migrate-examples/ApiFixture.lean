import Lean

/-! Isolated API fixture for the parser/elaborator/evaluator and generated theorem
patterns in SourceCounterexample, Tactics/FiniteSets and Tactics/Step. This tests
Lean APIs only; it establishes no Solidity program property. -/
namespace H62MigrateExamplesCompatibility
open Lean Elab Command Meta

run_cmd liftTermElabM do
  let parsed ← match Parser.runParserCategory (← getEnv) `term "(7 : Nat)" with
    | .ok stx => pure stx
    | .error message => throwError "fixture parser failed: {message}"
  let expression ← Term.elabTerm parsed (some (mkConst ``Nat))
  let expression ← instantiateMVars expression
  let decoded ← evalExpr Nat (mkConst ``Nat) expression
  unless decoded == 7 do throwError "fixture decoder changed the literal"
  let statement ← mkEq expression expression
  let proof ← mkEqRefl expression
  let proofType ← inferType proof
  unless (← isDefEq proofType statement) do throwError "generated proof changed type"
  let falseStatement ← mkEq (mkNatLit 7) (mkNatLit 8)
  if (← isDefEq proofType falseStatement) then throwError "false equality type accepted"
  let name := `H62MigrateExamplesCompatibility.generatedSeven
  addDecl <| .thmDecl {name, levelParams := [], type := statement, value := proof}

/-- The generated declaration must be consumable at its exact equality type. -/
example : (7 : Nat) = 7 := generatedSeven
#print axioms generatedSeven
end H62MigrateExamplesCompatibility
