import Solidity.Calculus.Core.DelabErase
import Solidity.Calculus.Core.Taclet
import Solidity.Calculus.Core.Proves

/-!
# Printing scoped taclets and formulas with schema variables

`Calculus/Core/Print.lean` prints a closed formula (`Core.Fml.show`, a value
in `MetaM`).  A taclet is not closed: its schema variables are free (`v`,
`se`, `thenStm`), so it is printed from its `Expr`, as `Rules.lean`'s
delaborators print today's taclets.  The `Expr` of a scoped statement,
premise or formula is translated into the `Expr` of its erasure, the
`Update.lean`/`Syntax.lean` term that `Fml.erase` would compute
(`Delab.tr`, `Calculus/Core/DelabErase.lean`, where the schema variables'
twins and the positions' names are explained), and printed with
`RuleSyntax.lean`'s printers (`ppStmt`, `ppPremise?`, `ppFml`): the same KeY
text, with no second printer to keep in step.  The end of a block in a
formula's frames prints `}` (`core_item`, below), the one piece of text
today's grammar has no production for.

The delaborators: `Core.Taclet C k m s p` as `dl{ ⟨[ s; ]⟩ ⇝ p }` (with
solkey's branch labels), a premise as `dl{ p }`, a formula as `dl{ φ }`; a
taclet's side conditions and carried proofs stay out of sight, as
`delabTacletSide` does for today's.
-/

namespace Solidity.Core

open Lean Meta PrettyPrinter Delaborator SubExpr
open Solidity (ppStmt ppPremise? ppFml ppOn isEscape fullApp)

/-! ## A block's end in a formula

Printing only: no macro reads it.  A modality's program with a `}` in it is
written with at least one `}`, so a program without one parses as today's
production alone. -/

/-- An item of a modality's program: a statement, or a block's end. -/
declare_syntax_cat core_item
syntax sol_stmt "; " : core_item
syntax "} " : core_item

/-- `⟨ s; … } ω ⟩ φ`: the program runs into the end of a block. -/
syntax:max "⟨ " (sol_stmt "; ")* "} " core_item* "⟩ " dl_fml:50 : dl_fml
/-- `[ s; … } ω ] φ` -/
syntax:max "[ " (sol_stmt "; ")* "} " core_item* "] " dl_fml:50 : dl_fml

namespace Delab

/-! ## Printing -/

/-- The statements of a modality's item list, if it is one: `(s ";")*`. -/
def stmtItems (stx : Syntax) : Array Syntax :=
  stx.getArgs.flatMap fun g =>
    if g.isAtom then #[]
    else if g.getKind == groupKind || g.isOfKind nullKind then #[g[0]] else #[g]

/-- Whether a printed statement is a block's end. -/
def isBlockEnd (s : Syntax) : Bool :=
  let x := if s.isIdent then s else s[0]
  x.isIdent && x.getId == blockEndName

/-- `⟨ … ⟩ φ` and `[ … ] φ` with a block's end among its statements, in the
grammar above (`}` without its `;`). -/
partial def fixBlockEnds (stx : Syntax) : MetaM Syntax := do
  let .node info k args := stx | return stx
  let args ← args.mapM fixBlockEnds
  let stx := Syntax.node info k args
  unless args.size == 4 && (args[0]!.isToken "⟨" || args[0]!.isToken "[") do return stx
  let ss := stmtItems args[1]!
  unless ss.any isBlockEnd do return stx
  let some i := ss.findIdx? isBlockEnd | return stx
  let pre : Array (TSyntax `sol_stmt) := (ss.extract 0 i).map (⟨·⟩)
  let rest ← (ss.extract (i + 1) ss.size).mapM fun s =>
    if isBlockEnd s then `(core_item| } ) else `(core_item| $(⟨s⟩):sol_stmt ; )
  let φ : TSyntax `dl_fml := ⟨args[3]!⟩
  if args[0]!.isToken "⟨" then
    return (← `(dl_fml| ⟨ $[$pre;]* } $rest* ⟩ $φ)).raw
  return (← `(dl_fml| [ $[$pre;]* } $rest* ] $φ)).raw

/-- A scoped formula with schema variables in it, in the notation. -/
def ppFmlE (e : Expr) : MetaM (TSyntax `dl_fml) :=
  withErased e true fun l => do return ⟨← fixBlockEnds (← ppFml l)⟩

/-- A scoped formula, one line. -/
def fmtFml (e : Expr) : MetaM String := do
  return (← PrettyPrinter.ppCategory `dl_fml (← ppFmlE e)).pretty 100000

/-! ## The delaborators -/

/-- The statements of an erased program with schema variables in it, a
program variable as a statement (`body;`). -/
def progItems? (P : Expr) : MetaM (Option (Array (TSyntax `sol_stmt))) := do
  let some (ss, t) ← Solidity.ppProgParts? P | return none
  match t with
  | some x => return some (ss.push (← `(sol_stmt| $x:ident)))
  | none => return some ss

/-- solkey's `blockEmpty`, scoped: a block of schema variables and the
statements it runs, `⟨[ { body; }; ]⟩ ⇝ ⟨[ body; ]⟩`.  Its locals' pop at the
end (`Premise.unfold`'s `Ext`) is what erasure loses, and prints as nothing,
as a frame's end does in a premise. -/
def blockLine? (e : Expr) : MetaM (Option (TSyntax `sol_stmt × TSyntax `dl_premise)) := do
  unless (← whnfR (e.getArg! 5)).isAppOf ``Stmt.block do return none
  withTwins (schema := true) e false fun env => do
    let st ← (tr [] (e.getArg! 5)).run env
    let p ← whnf ((← (tr [] (e.getArg! 6)).run env))
    unless p.isAppOf ``Solidity.Premise.unfold do return none
    let (some ss, some ps) := (← progItems? st, ← progItems? p.appArg!) | return none
    return some (← `(sol_stmt| { $[$ss;]* }), ← `(dl_premise| ⟨[ $[$ps;]* ]⟩))

/-- `Core.Taclet C k m s p`: `dl{ ⟨[ s; ]⟩ ⇝ p }`, as `delabTaclet` prints
today's, its goals labelled by solkey's labels. -/
@[delab app.Solidity.Core.Taclet]
def delabTaclet : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 7)
  let m ← whnf (e.getArg! 2)
  if let some (s, p) ← blockLine? e then
    return ← match_expr m with
      | Modality.box => `(dl{ [ $s:sol_stmt; ] ⇝ $p })
      | Modality.diamond => `(dl{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
      | _ => `(dl{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })
  let out? ← withTwins (schema := true) e false fun env => do
      let st ← (tr [] (e.getArg! 5)).run env
      let p ← (tr [] (e.getArg! 6)).run env
      let st' ← whnf st
      let rule? := Solidity.Taclet.labelledBy (st'.getAppFn.constName?.getD Lean.Name.anonymous)
        (m.isConstOf ``Modality.diamond)
      let labels := (do (← Solidity.Taclet.branchLabels.lookup (← rule?))).getD []
      let some p ← ppPremise? p labels (m.isConstOf ``Modality.box) | return none
      return some (← ppStmt st, p)
  let some (s, p) := out? | failure
  if isEscape s then failure
  match_expr m with
  | Modality.box => `(dl{ [ $s:sol_stmt; ] ⇝ $p })
  | Modality.diamond => `(dl{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
  | _ => `(dl{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })

/-- A scoped premise standing alone: `dl{ p }`. -/
def delabPremise : Delab := do
  unless ← ppOn do failure
  fullApp
  let e ← getExpr
  let some p ← withErased e false fun l => ppPremise? l | failure
  `(dl{ $p:dl_premise })

attribute [delab app.Solidity.Core.Premise.update, delab app.Solidity.Core.Premise.unfold,
  delab app.Solidity.Core.Premise.bind, delab app.Solidity.Core.Premise.split,
  delab app.Solidity.Core.Premise.check, delab app.Solidity.Core.Premise.done,
  delab app.Solidity.Core.Premise.branches, delab app.Solidity.Core.Premise.cases,
  delab app.Solidity.Core.Premise.inv, delab app.Solidity.Core.Premise.inline] delabPremise

/-- A scoped formula standing alone: `dl{ φ }`, a block's end `}`. -/
def delabFml : Delab := do
  unless ← ppOn do failure
  fullApp
  let φ ← ppFmlE (← getExpr)
  guard !(isEscape φ)
  `(dl{ $φ:dl_fml })

attribute [delab app.Solidity.Core.Fml.eq, delab app.Solidity.Core.Fml.defined,
  delab app.Solidity.Core.Fml.not, delab app.Solidity.Core.Fml.and,
  delab app.Solidity.Core.Fml.imp, delab app.Solidity.Core.Fml.upd,
  delab app.Solidity.Core.Fml.modal, delab app.Solidity.Core.Fml.all,
  delab app.Solidity.Core.Fml.bind, delab app.Solidity.Core.Fml.havoc,
  delab app.Solidity.Core.Fml.anon] delabFml

/-! ## Sequents -/

/-- A sequent's context, erased: the rest `..H` when it is a variable, the
entries as `Calculus/Hyp.lean`'s `Hyp`s, and the names of the last scope.  What
erasure loses prints as nothing: an update of pops only, and the hidden
binder (it only names the local it puts in scope). -/
partial def hypsParts (c H : Expr) : TrM (Option Lean.Name × Array Expr × List Expr) := do
  let H := (← instantiateMVars H).consumeMData
  let unknown (Γ : Expr) : MetaM (List Expr) := do
    return List.replicate ((← ctxLength? Γ).getD 0) unknownVar
  if let .fvar fv := H then
    let ty ← whnfR (← fv.getType)
    return (some (← fv.getDecl).userName, #[], ← unknown (ty.getArg! 2))
  let H ← whnf H
  let args := H.getAppArgs
  match H.getAppFn.constName? with
  | some ``Hyps.nil => return (none, #[], ← unknown args[1]!)
  | some ``Hyps.pre =>
    let (r, hs, ns) ← hypsParts c args[3]!
    return (r, hs.push (mkApp2 (mkConst ``Solidity.Hyp.pre) c (← tr ns args[4]!)), ns)
  | some ``Hyps.upd =>
    let (r, hs, ns) ← hypsParts c args[4]!
    let (es, ms) ← updParts ns args[6]!
    if es.isEmpty then return (r, hs, ms)
    let U ← updList c args[6]! es
    return (r, hs.push (mkApp3 (mkConst ``Solidity.Hyp.upd) c args[5]! U), ms)
  | some ``Hyps.havoc =>
    let (r, hs, ns) ← hypsParts c args[3]!
    return (r, hs.push (mkApp (mkConst ``Solidity.Hyp.havoc) c), ns)
  | some ``Hyps.all =>
    let (r, hs, ns) ← hypsParts c args[3]!
    return (r, hs.push (mkApp3 (mkConst ``Solidity.Hyp.all) c args[4]! args[5]!), args[4]! :: ns)
  | some ``Hyps.bind =>
    let (r, hs, ns) ← hypsParts c args[3]!
    return (r, hs, args[5]! :: ns)
  | some ``Hyps.anon =>
    let (r, hs, ns) ← hypsParts c args[3]!
    let some xs ← Solidity.listElems? args[4]! | throwError "anon"
    let xs ← xs.mapM fun x => do trIdx ns (← whnf x).appArg!
    let xs ← mkListLit (mkConst ``Solidity.Var) xs.toList
    return (r, hs.push (mkApp2 (mkConst ``Solidity.Hyp.anon) c xs), ns)
  | _ => throwError "not a context"

/-- `Core.Proves C R Γ₀ H φ`: the sequent `dl{ ..H, h₁, … ⟹ φ }`, as
`delabProves` prints today's (`⟹ₖ` for solkey's rules alone, `⟹[R]` over
a variable rule set), its context's entries erased (`hypsParts`). -/
@[delab app.Solidity.Core.Proves]
def delabProves : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 6)
  let c := e.getArg! 0
  let R ← whnf (e.getArg! 1)
  let out? ← withTwins (contract? := some c) e true fun env => do
    let some (rest, hs, ns) ← (try some <$> (hypsParts c (e.getArg! 4)).run env catch _ => pure none)
      | return none
    let φ ← (tr ns (e.getArg! 5)).run env
    let mut out : Array (TSyntax `dl_hyp) := #[]
    if let some r := rest then out := out.push (← `(dl_hyp| ..$(mkIdent r):ident))
    for h in hs do
      let some h ← Solidity.ppHyp? h | return none
      out := out.push ⟨← fixBlockEnds h⟩
    return some (out, (⟨← fixBlockEnds (← ppFml φ)⟩ : TSyntax `dl_fml))
  let some (out, φ) := out? | failure
  guard !(isEscape φ)
  if R.isConstOf ``RuleSet.all then `(dl{ $[$out],* ⟹ $φ:dl_fml })
  else if R.isConstOf ``RuleSet.solkey then `(dl{ $[$out],* ⟹ₖ $φ:dl_fml })
  else if let some r ← Solidity.fvarName? R then `(dl{ $[$out],* ⟹[$(Solidity.nameIdent r)] $φ:dl_fml })
  else failure

/-- The side condition `CallRet.isRets ret = b` of a scoped taclet's type,
its `b`. -/
partial def callSide : Expr → Option Expr
  | .forallE _ t b _ =>
    if t.isAppOfArity ``autoParam 2 then
      match (t.getArg! 0).eq? with
      | some (_, l, r) => if l.isAppOf ``CallRet.isRets then some r else callSide b
      | none => callSide b
    else callSide b
  | _ => none

/-- A scoped taclet's type: its side conditions and carried proofs out of
sight, as today's `delabTacletSide` had them, a call without targets
printed `ic` (`pp.sol.ic`). -/
@[delab forallE]
def delabTacletSide : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  let b := e.getForallBody
  -- `Core.CallbackTaclet` is declared by a module importing this one (`Core/Callback.lean`)
  unless b.isAppOf ``Core.Taclet || b.isAppOf ``Core.LeanTaclet ||
      b.isAppOf `Solidity.Core.CallbackTaclet do failure
  -- a call without targets is KeY's `ic` (`hrets : CallRet.isRets ret = false`)
  let ic := (callSide e).any (·.isConstOf ``Bool.false)
  withTheReader Lean.Core.Context (fun c => { c with options := c.options.setBool `pp.sol.ic ic }) <|
    withTheReader SubExpr (fun s => { s with expr := Solidity.dropSide e })
      (Solidity.delabTacletBinders #[] #[])

end Delab

end Solidity.Core

