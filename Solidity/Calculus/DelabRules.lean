import Solidity.Calculus.PrintStmt
import Solidity.Calculus.Taclet

/-!
# Printing scoped taclets and formulas with schema variables

`Calculus/Print.lean` prints a closed formula (`Fml.show`, a value
in `MetaM`).  A taclet is not closed: its schema variables are free (`v`,
`se`, `thenStm`), so it is printed from its `Expr`, by
`Calculus/PrintStmt.lean`'s printer of the scoped syntax (`ppStmtS`,
`ppPremiseS`, `ppFmlS`): positions are the names their binders gave them, a
schema variable its own name, terms and updates printed by
`Calculus/PrintTerm.lean`'s printers of the scoped terms, with
`RuleSyntax.lean`'s builders, so the KeY text is
the one the rule lines write.  The end of a block in a formula's frames
prints `}` (`core_item`, below), the one piece of text the grammar of
`RuleSyntax.lean` has no production for.

The delaborators: `Taclet C k m s p` as `dl{ ⟨[ s; ]⟩ ⇝ p }` (with
solkey's branch labels), a premise as `dl{ p }`, a formula as `dl{ φ }`; a
taclet's side conditions and carried proofs stay out of sight, as
`delabTacletSide` does.  A sequent's printer is `Calculus/Delab.lean`'s,
above the judgement; these sit below it, beside the rule table.
-/

namespace Solidity

open Lean Meta PrettyPrinter Delaborator SubExpr
open Solidity (ppOn isEscape fullApp)

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

/-- A scoped formula with schema variables in it, in the notation, with its
`where` clause: a memory local a copy out of storage binds (`carol =
alice;`, what `memoryLocalDeclInitDrop` leaves of `Person memory carol =
alice;`) under a hidden binder, `φ where Person memory carol`, since a line
is read on its own and `storageLocalDeclInitDrop` leaves the same line of
`Person storage carol = alice;`. -/
def ppFmlE (e : Expr) : MetaM (TSyntax `dl_fml) := do
  let w : Wheres := { hidden := ← IO.mkRef #[], copied := ← IO.mkRef #[] }
  let φ : TSyntax `dl_fml := ⟨← fixBlockEnds (← withPrinter e true (ppFmlS [] e) (wheres := w))⟩
  let hidden ← w.hidden.get
  let mut seen : Array Expr := #[]
  let mut ds : Array (TSyntax `sol_stmt) := #[]
  for x in ← w.copied.get do
    if seen.contains x then continue
    let some (_, R) := hidden.find? (·.1 == x) | continue
    seen := seen.push x
    let some xi ← Solidity.ppVar? x | continue
    ds := ds.push (← `(sol_stmt| $(← Solidity.ppTy.ppRef R):sol_ty memory $xi:ident))
  if ds.isEmpty then return φ
  `(dl_fml| $φ:dl_fml where $ds,*)

/-- A scoped formula, one line. -/
def fmtFml (e : Expr) : MetaM String := do
  return (← PrettyPrinter.ppCategory `dl_fml (← ppFmlE e)).pretty 100000

/-! ## The delaborators -/

/-- solkey's `blockEmpty`, scoped: a block of schema variables and the
statements it runs, `⟨[ { body; }; ]⟩ ⇝ ⟨[ body; ]⟩`.  Its locals' pop at the
end (`Premise.unfold`'s `Ext`) prints as nothing, as a frame's end does in a
premise. -/
def blockLine? (e : Expr) : MetaM (Option (TSyntax `sol_stmt × TSyntax `dl_premise)) := do
  let s ← whnfR (e.getArg! 5)
  unless s.isAppOf ``Stmt.block do return none
  withPrinter e false do
    let p ← whnf (e.getArg! 6)
    let ps ← if p.isAppOfArity ``Premise.unfold 6 || p.isAppOfArity ``Premise.inline 6 then
        progExprPieces [] (p.getArg! 4)
      else if p.isAppOfArity ``Premise.bind 6 then progExprPieces [p.getArg! 3] (p.getArg! 5)
      else return none
    let (some ss, some ps) := (← progItemsS (← progPiecesS [] s.appArg!).1, ← progItemsS ps)
      | return none
    return some (← `(sol_stmt| { $[$ss;]* }), ← `(dl_premise| ⟨[ $[$ps;]* ]⟩))

/-- A rule's statement `s` and premise `p` under the modality `m`, printed,
the goals labelled by solkey's labels: those of the taclet the statement's
head names (`Taclet.labelledBy`), or with `inv` of `whileInvariantBox` for an
invariant premise. -/
def tacletLine? (e s p m : Expr) (inv : Bool := false) :
    MetaM (Option (TSyntax `sol_stmt × TSyntax `dl_premise)) :=
  withPrinter e false do
    let p' ← whnf p
    let s' ← whnf s
    let rule? := if inv && p'.isAppOf ``Premise.inv then some "whileInvariantBox"
      else Solidity.Taclet.labelledBy (labelHead s') (m.isConstOf ``Modality.diamond)
    let labels := (do (← Solidity.Taclet.branchLabels.lookup (← rule?))).getD []
    let nativePush := s'.isAppOf ``Stmt.pushOpAssign || s'.isAppOf ``Stmt.pushIncDec
    let some p ← withOptions (fun o => o.setBool `pp.sol.pushArithmetic nativePush)
      (ppPremiseS [] p labels (m.isConstOf ``Modality.box)) | return none
    return some (← ppStmtS [] s, p)

/-- `Taclet C k m s p` as `dl{ ⟨[ s; ]⟩ ⇝ p }` (none where it does not
print). -/
def tacletTerm? (e : Expr) : MetaM (Option Lean.Term) := do
  let m ← whnf (e.getArg! 2)
  let mkTerm (l : TSyntax `sol_stmt × TSyntax `dl_premise) : MetaM Lean.Term := do
    let (s, p) := l
    match_expr m with
    | Modality.box => `(dl{ [ $s:sol_stmt; ] ⇝ $p })
    | Modality.diamond => `(dl{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
    | _ => `(dl{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })
  if let some l ← blockLine? e then
    return some (← mkTerm l)
  let some l ← tacletLine? e (e.getArg! 5) (e.getArg! 6) m (inv := true) | return none
  if isEscape l.1 then return none
  return some (← mkTerm l)

/-- `Taclet C k m s p`: `dl{ ⟨[ s; ]⟩ ⇝ p }`, its goals labelled by solkey's
labels. -/
@[delab app.Solidity.Taclet]
def delabTaclet : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 7)
  let some t ← tacletTerm? e | failure
  return t

/-- A scoped premise standing alone: `dl{ p }`. -/
def delabPremise : Delab := do
  unless ← ppOn do failure
  fullApp
  let e ← getExpr
  let some p ← withPrinter e false (ppPremiseS [] e) | failure
  `(dl{ $p:dl_premise })

attribute [delab app.Solidity.Premise.update, delab app.Solidity.Premise.updates,
  delab app.Solidity.Premise.guardedUpdates,
  delab app.Solidity.Premise.unfold,
  delab app.Solidity.Premise.bind, delab app.Solidity.Premise.split,
  delab app.Solidity.Premise.check, delab app.Solidity.Premise.done,
  delab app.Solidity.Premise.branches, delab app.Solidity.Premise.cases,
  delab app.Solidity.Premise.inv, delab app.Solidity.Premise.inline] delabPremise

/-- A scoped formula standing alone: `dl{ φ }`, a block's end `}`. -/
def delabFml : Delab := do
  unless ← ppOn do failure
  fullApp
  let φ ← ppFmlE (← getExpr)
  guard !(isEscape φ)
  `(dl{ $φ:dl_fml })

attribute [delab app.Solidity.Fml.eq, delab app.Solidity.Fml.wellFormed,
  delab app.Solidity.Fml.not, delab app.Solidity.Fml.and,
  delab app.Solidity.Fml.imp, delab app.Solidity.Fml.upd,
  delab app.Solidity.Fml.modal, delab app.Solidity.Fml.all,
  delab app.Solidity.Fml.bind, delab app.Solidity.Fml.havoc,
  delab app.Solidity.Fml.anon] delabFml

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
  -- `CallbackTaclet` is declared by a module importing this one (`Callback.lean`)
  unless b.isAppOf ``Taclet || b.isAppOf ``LeanTaclet ||
      b.isAppOf `Solidity.CallbackTaclet do failure
  -- a call without targets is KeY's `ic` (`hrets : CallRet.isRets ret = false`)
  let ic := (callSide e).any (·.isConstOf ``Bool.false)
  withTheReader Lean.Core.Context (fun c => { c with options := c.options.setBool `pp.sol.ic ic }) <|
    withTheReader SubExpr (fun s => { s with expr := Solidity.dropSide e })
      (Solidity.delabTacletBinders #[] #[])

end Delab

end Solidity

