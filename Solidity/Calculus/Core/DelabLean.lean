import Solidity.Calculus.Core.Delab

/-!
# Printing the scoped rules solkey does not have

`Calculus/Core/Delab.lean`'s printer for `Core.Taclet`, for the other scoped
judgement, `Core.LeanTaclet` (`Calculus/Core/Rules.lean`): the rule as
`dl[LeanTaclet C k]{ ⟨[ s; ]⟩ ⇝ p }`, its statement and premise erased with
their schema variables (`Core.Delab.tr`, `Calculus/Core/DelabErase.lean`) and printed by `Rules.lean`'s
printers, a loop's invariant rule with solkey's branch labels.
-/

namespace Solidity.Core.Delab

open Lean Meta PrettyPrinter Delaborator SubExpr
open Solidity (ppStmt ppPremise? ppOn isEscape escapeTerm)

/-- `functionCallArgCapture`'s premise (`Premise.argCapture`, blocked on its
schema variable `ret`): `⟨[ T se = v; ‹Core.Stmt.call f as' ret body›; ]⟩`,
the capture as `Syntax.lean` writes it and the call with the captured
arguments as a term, as `Rules.lean` prints today's rule. -/
def argCapturePremise? (p : Expr) : MetaM (Option (TSyntax `dl_premise)) := do
  let p ← instantiateMVars p
  unless p.isAppOfArity ``Solidity.Core.Premise.argCapture 13 do return none
  let a := p.getAppArgs
  let c := a[0]!
  withTwins p false fun env => do
    let v ← (tr [] a[9]!).run env
    let x := mkApp2 (mkConst ``Solidity.Var.fresh) (toExpr "se") a[2]!
    let init := mkApp2 (mkConst ``Option.some [levelZero]) (mkApp2 (mkConst ``Solidity.Val) c a[8]!) v
    let decl ← ppStmt (mkApp4 (mkConst ``Solidity.Surface.Stmt.declLocal) c a[8]! x init)
    let call := mkIdent (← unresolveNameGlobal ``Solidity.Core.Stmt.call)
    let t ← `($call $(← escapeTerm a[3]!) $(← escapeTerm a[10]!) $(← escapeTerm a[11]!)
      $(← escapeTerm a[12]!))
    let call ← `(sol_stmt| ‹$t:term›)
    return some (← `(dl_premise| ⟨[ $decl:sol_stmt; $call:sol_stmt; ]⟩))

/-- `Core.LeanTaclet C k m s p`: `dl[LeanTaclet C k]{ ⟨[ s; ]⟩ ⇝ p }`, as
`Rules.lean`'s `delabTaclet` prints today's. -/
@[delab app.Solidity.Core.LeanTaclet]
def delabLeanTaclet : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 7)
  let m ← whnf (e.getArg! 2)
  let J ← `($(mkIdent (← unresolveNameGlobal ``LeanTaclet))
    $((← (List.range 2).toArray.mapM fun i => withNaryArg i delab))*)
  if let some p ← argCapturePremise? (e.getArg! 6) then
    -- the call, its arguments a schema variable, as a term (`‹…›`)
    let s ← `(sol_stmt| ‹$(← escapeTerm (e.getArg! 5)):term›)
    return ← `(dl[ $J ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })
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
  match_expr m with
  | Modality.box => `(dl[ $J ]{ [ $s:sol_stmt; ] ⇝ $p })
  | Modality.diamond => `(dl[ $J ]{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
  | _ => `(dl[ $J ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })

end Solidity.Core.Delab
