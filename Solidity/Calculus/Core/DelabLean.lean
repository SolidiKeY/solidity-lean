import Solidity.Calculus.Core.Delab

/-!
# Printing the scoped rules solkey does not have

`Calculus/Core/Delab.lean`'s printer for `Core.Taclet`, for the other scoped
judgement, `Core.LeanTaclet` (`Calculus/Core/Rules.lean`): the rule as
`dl[LeanTaclet C k]{ ⟨[ s; ]⟩ ⇝ p }`, its statement and premise erased with
their schema variables (`Core.Delab.tr`) and printed by `Rules.lean`'s
printers, a loop's invariant rule with solkey's branch labels.
-/

namespace Solidity.Core.Delab

open Lean Meta PrettyPrinter Delaborator SubExpr
open Solidity (ppStmt ppPremise? ppOn isEscape)

/-- `Core.LeanTaclet C k m s p`: `dl[LeanTaclet C k]{ ⟨[ s; ]⟩ ⇝ p }`, as
`Rules.lean`'s `delabTaclet` prints today's. -/
@[delab app.Solidity.Core.LeanTaclet]
def delabLeanTaclet : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 7)
  let m ← whnf (e.getArg! 2)
  let out? ← withTwins e false fun env => do
    let st ← (tr [] (e.getArg! 5)).run env
    let p ← (tr [] (e.getArg! 6)).run env
    let st' ← whnf st
    -- a loop's goals are labelled by the rule its annotation picks
    let rule? : Option String := if p.isAppOf ``Solidity.Premise.inv then some "whileInvariantBox"
      else Solidity.Taclet.labelledBy (st'.getAppFn.constName?.getD Lean.Name.anonymous)
        (m.isConstOf ``Modality.diamond)
    let labels := (do (← Solidity.Taclet.branchLabels.lookup (← rule?))).getD []
    let some p ← ppPremise? p labels (m.isConstOf ``Modality.box) | return none
    return some (← ppStmt st, p)
  let some (s, p) := out? | failure
  if isEscape s then failure
  let args ← (List.range 2).toArray.mapM fun i => withNaryArg i delab
  let J ← `($(mkIdent (← unresolveNameGlobal ``LeanTaclet)) $args*)
  match_expr m with
  | Modality.box => `(dl[ $J ]{ [ $s:sol_stmt; ] ⇝ $p })
  | Modality.diamond => `(dl[ $J ]{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
  | _ => `(dl[ $J ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })

end Solidity.Core.Delab
