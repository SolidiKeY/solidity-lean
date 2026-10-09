import Solidity.Calculus.Core.Delab

/-!
# Printing the scoped rules solkey does not have

`Calculus/Core/Delab.lean`'s printer for `Core.Taclet`, for the other scoped
judgement, `Core.LeanTaclet` (`Calculus/Core/Rules.lean`): the rule as
`dl[LeanTaclet C k]{ ⟨[ s; ]⟩ ⇝ p }`, its statement and premise erased with
their schema variables (`Core.Delab.tr`, `Calculus/Core/DelabErase.lean`) and printed by today's printers
(`Calculus/RuleSyntax.lean`), a loop's invariant rule with solkey's branch
labels.
-/

namespace Solidity.Core.Delab

open Lean Meta PrettyPrinter Delaborator SubExpr
open Solidity (ppStmt ppPremise? ppOn isEscape escapeTerm)

/-- `Arg.separatedFrom [] as = true`, of today's arguments `as`. -/
def sepTy (c as : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool)
    (mkApp3 (mkConst ``Solidity.Arg.separatedFrom) c (mkApp (mkConst ``List.nil [levelZero])
      (mkConst ``Solidity.Var)) as) (mkConst ``Bool.true)

/-- `functionCallArgCapture`, its call `s` and premise `p`
(`Premise.argCapture`, blocked on its schema variable `ret`), as today's
table printed the rule: the call as today's term of the twins
(`‹Surface.Stmt.call f args hsep ret body›`; a call of schema variables
whose arguments are not all simple is neither `fbs` nor `ic`), the premise
`⟨[ T se = v; ‹Surface.Stmt.call f as' ⋯ ret body›; ]⟩`, the capture as
`Syntax.lean` writes it and the call with the captured arguments as a term. -/
def argCapture? (s p : Expr) :
    MetaM (Option (TSyntax `sol_stmt × TSyntax `dl_premise)) := do
  let p ← instantiateMVars p
  let s ← instantiateMVars s
  unless p.isAppOfArity ``Solidity.Core.Premise.argCapture 13 do return none
  unless s.isAppOfArity ``Solidity.Core.Stmt.call 10 do return none
  let a := p.getAppArgs
  let c := a[0]!
  withTwins (schema := true) (mkApp2 (mkConst ``Prod.mk [levelZero, levelZero]) s p) false fun env => do
    let tw (x : Expr) : MetaM (Option Expr) := (twin? x).run env
    let (some as, some ret, some body, some as') :=
        (← tw (s.getArg! 7), ← tw (s.getArg! 8), ← tw (s.getArg! 9), ← tw a[10]!) | return none
    let v ← (tr [] a[9]!).run env
    let x := mkApp2 (mkConst ``Solidity.Var.fresh) (toExpr "se") a[2]!
    let init := mkApp2 (mkConst ``Option.some [levelZero]) (mkApp2 (mkConst ``Solidity.Val) c a[8]!) v
    let decl ← ppStmt (mkApp4 (mkConst ``Solidity.Surface.Stmt.declLocal) c a[8]! x init)
    withLocalDeclD `hsep (sepTy c as) fun hsep => do
      let call (as h : Expr) : MetaM (TSyntax `sol_stmt) := do
        let t ← escapeTerm (mkAppN (mkConst ``Solidity.Surface.Stmt.call) #[c, a[3]!, as, h, ret, body])
        `(sol_stmt| ‹$t:term›)
      let st ← call as hsep
      let st' ← call as' hsepPlaceholder
      return some (st, ← `(dl_premise| ⟨[ $decl:sol_stmt; $st':sol_stmt; ]⟩))

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
  if let some (s, p) ← argCapture? (e.getArg! 5) (e.getArg! 6) then
    return ← `(dl[ $J ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })
  let out? ← withTwins (schema := true) e false fun env => do
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
