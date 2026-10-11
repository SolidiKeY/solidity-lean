import Solidity.Calculus.Delab

/-!
# Printing the scoped rules solkey does not have

`Calculus/Delab.lean`'s printer for `Taclet`, for the other scoped
judgement, `LeanTaclet` (`Calculus/Rules.lean`): the rule as
`dl[LeanTaclet C k]{ ⟨[ s; ]⟩ ⇝ p }`, its statement and premise printed by
`Calculus/PrintStmt.lean`'s printer of the scoped syntax (`tacletLine?`), a
loop's invariant rule with solkey's branch labels.  `functionCallArgCapture`'s
calls print as terms (`argCapture?`): a call whose arguments are not all
simple has no line of KeY's.
-/

namespace Solidity.Delab

open Lean Meta PrettyPrinter Delaborator SubExpr
open Solidity (ppOn isEscape escapeTerm ppVar? ppTy)

/-- `functionCallArgCapture`, its call `s` and premise `p`
(`Premise.argCapture`, blocked on its schema variable `ret`): the call as a
term (`‹Stmt.call f args ret body›`; a call of schema variables whose
arguments are not all simple is neither `fbs` nor `ic`, and has no line of
KeY's), the premise `⟨[ T se = v; ‹Stmt.call f as' ret body›; ]⟩`, the
capture as the rule writes it and the call with the captured arguments as
a term. -/
def argCapture? (s p : Expr) :
    MetaM (Option (TSyntax `sol_stmt × TSyntax `dl_premise)) := do
  let p ← instantiateMVars p
  let s ← instantiateMVars s
  unless p.isAppOfArity ``Solidity.Premise.argCapture 13 do return none
  unless s.isAppOfArity ``Solidity.Stmt.call 10 do return none
  let a := p.getAppArgs
  let x := mkApp2 (mkConst ``Solidity.Var.fresh) (toExpr "se") a[2]!
  let some xi ← ppVar? x | return none
  let decl ← `(sol_stmt| $(← ppTy.ppPrim a[8]!):sol_ty $xi:ident = $(← ppExprS [] a[9]!):sol_expr)
  let call (t : Expr) : MetaM (TSyntax `sol_stmt) := do `(sol_stmt| ‹$(← escapeTerm t):term›)
  -- the call with the captured arguments `as'`, printing only
  let st' ← call (mkAppN s.getAppFn (s.getAppArgs.set! 7 a[10]!))
  return some (← call s, ← `(dl_premise| ⟨[ $decl:sol_stmt; $st':sol_stmt; ]⟩))

/-- `LeanTaclet C k m s p`: `dl[LeanTaclet C k]{ ⟨[ s; ]⟩ ⇝ p }`, as
`Rules.lean`'s `delabTaclet` prints today's. -/
@[delab app.Solidity.LeanTaclet]
def delabLeanTaclet : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 7)
  let m ← whnf (e.getArg! 2)
  let J ← `($(mkIdent (← unresolveNameGlobal ``LeanTaclet))
    $((← (List.range 2).toArray.mapM fun i => withNaryArg i delab))*)
  if let some (s, p) ← argCapture? (e.getArg! 5) (e.getArg! 6) then
    return ← `(dl[ $J ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })
  let some (s, p) ← tacletLine? e (e.getArg! 5) (e.getArg! 6) m (inv := true) | failure
  if isEscape s then failure
  match_expr m with
  | Modality.box => `(dl[ $J ]{ [ $s:sol_stmt; ] ⇝ $p })
  | Modality.diamond => `(dl[ $J ]{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
  | _ => `(dl[ $J ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })

end Solidity.Delab
