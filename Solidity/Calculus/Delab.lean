import Solidity.Calculus.PrintStmt
import Solidity.Calculus.Taclet
import Solidity.Calculus.Proves

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
solkey's branch labels), a premise as `dl{ p }`, a formula as `dl{ φ }`, a
sequent as `dl{ ..H, h ⟹ φ }`; a taclet's side conditions and carried
proofs stay out of sight, as `delabTacletSide` does.
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
    let some p ← ppPremiseS [] p labels (m.isConstOf ``Modality.box) | return none
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
  let some l ← tacletLine? e (e.getArg! 5) (e.getArg! 6) m | return none
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

attribute [delab app.Solidity.Premise.update, delab app.Solidity.Premise.unfold,
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

attribute [delab app.Solidity.Fml.eq, delab app.Solidity.Fml.defined,
  delab app.Solidity.Fml.not, delab app.Solidity.Fml.and,
  delab app.Solidity.Fml.imp, delab app.Solidity.Fml.upd,
  delab app.Solidity.Fml.modal, delab app.Solidity.Fml.all,
  delab app.Solidity.Fml.bind, delab app.Solidity.Fml.havoc,
  delab app.Solidity.Fml.anon] delabFml

/-! ## Sequents -/

/-- An update `U` of a sequent's context, of pieces `ps`, produced under `m`,
as `Calculus/Hyp.lean`'s `ppHyp?` prints the closer's: `{U}`, or `{U} [ ]`
and `{U} ⟨ ⟩` for a rule's update at a fixed modality; none where it
escapes (it would read back as a precondition). -/
def updHypS (m U : Expr) (ps : Array UPiece) : MetaM (Option (TSyntax `dl_hyp)) := do
  let u ← ppUpdPiecesS U ps
  if Solidity.isEscape u then return none
  if ← updHasSchemaVar U then
    match_expr (← whnf m) with
    | Modality.box => return some (← `(dl_hyp| $u:dl_upd [ ]))
    | Modality.diamond => return some (← `(dl_hyp| $u:dl_upd ⟨ ⟩))
    | _ => pure ()
  return some (← `(dl_hyp| $u:dl_upd))

/-- A sequent's context for the scoped printer: the rest `..H` when it is a
variable, the entries printed (a precondition by `ppFmlS`, an update by
`updHypS`, the rest as `Calculus/Hyp.lean`'s `Hyp`s), and the names of the last
scope.  What prints as nothing: an update of pops only, and the hidden
binder.  An error where an entry does not print. -/
partial def hypsPartsS (c H : Expr) : PrM (Option Lean.Name × Array (TSyntax `dl_hyp) × List Expr) := do
  let H := (← instantiateMVars H).consumeMData
  let unknown (Γ : Expr) : MetaM (List Expr) := do
    return List.replicate ((← ctxLength? Γ).getD 0) unknownVar
  let hyp (h : Expr) : MetaM (TSyntax `dl_hyp) := do
    let some h ← Solidity.ppHyp? h | throwError "an entry that does not print"
    return h
  if let .fvar fv := H then
    let ty ← whnfR (← fv.getType)
    return (some (← fv.getDecl).userName, #[], ← unknown (ty.getArg! 2))
  let H ← whnf H
  let args := H.getAppArgs
  match H.getAppFn.constName? with
  | some ``Hyps.nil => return (none, #[], ← unknown args[1]!)
  | some ``Hyps.pre =>
    let (r, hs, ns) ← hypsPartsS c args[3]!
    return (r, hs.push (← `(dl_hyp| $(← ppFmlS ns args[4]!):dl_fml)), ns)
  | some ``Hyps.upd =>
    let (r, hs, ns) ← hypsPartsS c args[4]!
    let U := args[6]!
    let (ps, ms) ← updPiecesS ns U
    if ps.isEmpty then return (r, hs, ms)
    let h ← updHypS args[5]! U ps
    if ← twinCheckOn then
      let (es, _) ← runTr (updParts ns U)
      let old ← Solidity.ppHyp? (mkApp3 (mkConst ``Solidity.Hyp.upd) c args[5]!
        (← runTr (updList c U es)))
      twinCompare "context update" (h.map (·.raw)) (old.map (·.raw)) `dl_hyp
    let some h := h | throwError "an entry that does not print"
    return (r, hs.push h, ms)
  | some ``Hyps.havoc =>
    let (r, hs, ns) ← hypsPartsS c args[3]!
    return (r, hs.push (← hyp (mkApp (mkConst ``Solidity.Hyp.havoc) c)), ns)
  | some ``Hyps.all =>
    let (r, hs, ns) ← hypsPartsS c args[3]!
    return (r, hs.push (← hyp (mkApp3 (mkConst ``Solidity.Hyp.all) c args[4]! args[5]!)),
      args[4]! :: ns)
  | some ``Hyps.bind =>
    let (r, hs, ns) ← hypsPartsS c args[3]!
    return (r, hs, args[5]! :: ns)
  | some ``Hyps.anon =>
    let (r, hs, ns) ← hypsPartsS c args[3]!
    let some xs ← Solidity.listElems? args[4]! | throwError "anon"
    let xs ← xs.mapM fun x => do idxName ns (← whnf x).appArg!
    let xs ← mkListLit (mkConst ``Solidity.Var) xs.toList
    return (r, hs.push (← hyp (mkApp2 (mkConst ``Solidity.Hyp.anon) c xs)), ns)
  | _ => throwError "not a context"

/-- The names of the last scope of a sequent's context `H` (`hypsPartsS`'s,
nothing printed). -/
partial def hypsNamesS (H : Expr) : PrM (List Expr) := do
  let H := (← instantiateMVars H).consumeMData
  let unknown (Γ : Expr) : MetaM (List Expr) := do
    return List.replicate ((← ctxLength? Γ).getD 0) unknownVar
  if let .fvar fv := H then return ← unknown ((← whnfR (← fv.getType)).getArg! 2)
  let H ← whnf H
  let args := H.getAppArgs
  match H.getAppFn.constName? with
  | some ``Hyps.nil => unknown args[1]!
  | some ``Hyps.pre | some ``Hyps.havoc | some ``Hyps.anon => hypsNamesS args[3]!
  | some ``Hyps.upd => return (← updShape (← hypsNamesS args[4]!) args[6]!).2
  | some ``Hyps.all => return args[4]! :: (← hypsNamesS args[3]!)
  | some ``Hyps.bind => return args[5]! :: (← hypsNamesS args[3]!)
  | _ => throwError "not a context"

/-- `Proves C R Γ₀ H φ` as a sequent; none where it does not print. -/
def provesTerm? (e : Expr) : MetaM (Option Lean.Term) := do
  let c := e.getArg! 0
  let R ← whnf (e.getArg! 1)
  let out? ← withPrinter (contract? := some c) e true do
    let some (rest, hs, ns) ← (try some <$> hypsPartsS c (e.getArg! 4) catch _ => pure none)
      | return none
    let φ ← ppFmlS ns (e.getArg! 5)
    let mut out : Array (TSyntax `dl_hyp) := #[]
    if let some r := rest then out := out.push (← `(dl_hyp| ..$(mkIdent r):ident))
    for h in hs do out := out.push ⟨← fixBlockEnds h⟩
    return some (out, (⟨← fixBlockEnds φ⟩ : TSyntax `dl_fml))
  let some (out, φ) := out? | return none
  if isEscape φ then return none
  if R.isConstOf ``RuleSet.all then return some (← `(dl{ $[$out],* ⟹ $φ:dl_fml }))
  else if R.isConstOf ``RuleSet.solkey then return some (← `(dl{ $[$out],* ⟹ₖ $φ:dl_fml }))
  else if let some r ← Solidity.fvarName? R then
    return some (← `(dl{ $[$out],* ⟹[$(Solidity.nameIdent r)] $φ:dl_fml }))
  else return none

/-- `Proves C R Γ₀ H φ`: the sequent `dl{ ..H, h₁, … ⟹ φ }` (`⟹ₖ` for
solkey's rules alone, `⟹[R]` over a variable rule set). -/
@[delab app.Solidity.Proves]
def delabProves : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 6)
  let some t ← provesTerm? e | failure
  return t

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

