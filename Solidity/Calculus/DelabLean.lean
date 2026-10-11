import Solidity.Calculus.Delab

/-!
# Printing the scoped rules solkey does not have

`Calculus/Delab.lean`'s printer for `Taclet`, for the other scoped
judgement, `LeanTaclet` (`Calculus/Rules.lean`): the rule as
`dl[LeanTaclet C k]{ ⟨[ s; ]⟩ ⇝ p }`, its statement and premise printed by
`Calculus/PrintStmt.lean`'s printer of the scoped syntax (`tacletLine?`), a
loop's invariant rule with solkey's branch labels.  `functionCallArgCapture`'s
calls print as the terms of their erasure's twins (`argCapture?`), as the
table has always printed that rule.
-/

namespace Solidity.Delab

open Lean Meta PrettyPrinter Delaborator SubExpr
open Solidity (ppOn isEscape escapeTerm ppVar? ppTy)

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
  unless p.isAppOfArity ``Solidity.Premise.argCapture 13 do return none
  unless s.isAppOfArity ``Solidity.Stmt.call 10 do return none
  let a := p.getAppArgs
  let c := a[0]!
  withTwins (schema := true) (mkApp2 (mkConst ``Prod.mk [levelZero, levelZero]) s p) false fun env => do
    let tw (x : Expr) : MetaM (Option Expr) := (twin? x).run env
    let (some as, some ret, some body, some as') :=
        (← tw (s.getArg! 7), ← tw (s.getArg! 8), ← tw (s.getArg! 9), ← tw a[10]!) | return none
    let x := mkApp2 (mkConst ``Solidity.Var.fresh) (toExpr "se") a[2]!
    let some xi ← ppVar? x | return none
    let decl ← `(sol_stmt| $(← ppTy.ppPrim a[8]!):sol_ty $xi:ident = $(← ppExprS [] a[9]!):sol_expr)
    withLocalDeclD `hsep (sepTy c as) fun hsep => do
      let call (as h : Expr) : MetaM (TSyntax `sol_stmt) := do
        let t ← escapeTerm (mkAppN (mkConst ``Solidity.Surface.Stmt.call) #[c, a[3]!, as, h, ret, body])
        `(sol_stmt| ‹$t:term›)
      let st ← call as hsep
      let st' ← call as' hsepPlaceholder
      return some (st, ← `(dl_premise| ⟨[ $decl:sol_stmt; $st':sol_stmt; ]⟩))

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
  let out? ← tacletLine? e (e.getArg! 5) (e.getArg! 6) m (inv := true)
  if ← twinCheckOn then
    let old? ← tacletLineLegacy? e (e.getArg! 5) (e.getArg! 6) m (inv := true)
    let fmt (l : Option (TSyntax `sol_stmt × TSyntax `dl_premise)) : MetaM String := do
      match l with
      | some (s, p) =>
        return s!"{← PrettyPrinter.ppCategory `sol_stmt s} ⇝ {← PrettyPrinter.ppCategory `dl_premise p}"
      | none => return "‹none›"
    let (a, b) := (← fmt out?, ← fmt old?)
    unless a == b do
      throwError m!"twin check (Lean taclet): the scoped printer prints\n{a}\nthe erasure's\n{b}"
  let some (s, p) := out? | failure
  if isEscape s then failure
  match_expr m with
  | Modality.box => `(dl[ $J ]{ [ $s:sol_stmt; ] ⇝ $p })
  | Modality.diamond => `(dl[ $J ]{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
  | _ => `(dl[ $J ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })

end Solidity.Delab
