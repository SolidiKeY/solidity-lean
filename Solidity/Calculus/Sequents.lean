import Solidity.Calculus.Hyp
import Solidity.Calculus.SurfaceNotation
import Solidity.Calculus.Surface
import Solidity.Calculus.Delab

/-!
# Checked sequent lines on scoped goals: `show sequent!{ Γ ⟹ φ }`

Today's `show sequent!{ Γ ⟹ φ }` (`Calculus/Sequents`, deleted at W4 `calc-del`), for a scoped goal
`H ⊢ φ` (`Proves`).  A scoped goal is not its text: its program
carries the frames the rules left (`pop`, `seq`, a hidden binder), which a
flat program read back does not have, so `show` cannot compare it by
unfolding.  The line is checked on what the goal **prints as**: its
erasure (`Delab.hypsParts`, `Delab.tr`, the frames' ends
dropped), against the line read as today's sequent (`elabSequent`), both
`Update.lean`'s terms, compared by unification.  So the line is written as
the goal prints, with today's spellings (`x == 1` for `x = 1`), without the
`}` of a block's end, and a hidden binder is no entry.

`show_sequent[C]{ Γ ⟹ φ }` and `show_sequent!{ Γ ⟹ φ }` are the checks;
under `open scoped Solidity.Scoped`, `show sequent!{ … }` and
`show sequent[C]{ … }` are them.  The goal is left as it is.
-/

namespace Solidity

open Lean Elab Term Meta Tactic

/-- `show_sequent[C]{ Γ ⟹ φ }`: the scoped goal prints as the sequent. -/
syntax (name := showSequent) "show_sequent" "[" term "]{ " sepBy(dl_hyp, ", ") seq_arrow dl_fml " }" :
  tactic
/-- `show_sequent!{ Γ ⟹ φ }`: `show_sequent[C]{ … }` for the file's
`InContract` contract. -/
syntax "show_sequent!" "{ " sepBy(dl_hyp, ", ") seq_arrow dl_fml " }" : tactic

/-- The goal `Proves C R Γ₀ H φ`, erased: its rule set, its context as
`Hyp.lean`'s entries and its formula, `k` run with them in scope. -/
def erasedGoal {α : Type} (ty : Expr) (k : Expr → Array Expr → Expr → MetaM α) : MetaM α := do
  let ty ← whnfR (← instantiateMVars ty)
  unless ty.isAppOfArity ``Proves 6 do throwError "show_sequent: not a scoped goal{indentExpr ty}"
  let c := ty.getArg! 0
  Delab.withTwins (contract? := some c) ty false fun env => do
    let (_, hs, ns) ← (Delab.hypsParts c (ty.getArg! 4)).run env
    let φ ← (Delab.tr ns (ty.getArg! 5)).run env
    k (ty.getArg! 1) hs φ

/-- The sequent's formula, written: `a → …` for a precondition, `{U} …`
for an update, `∀ T x; …` for a quantified local. -/
def sequentFmlC (hs : Array (TSyntax `dl_hyp)) (φ : TSyntax `dl_fml) :
    MacroM (TSyntax `dl_fml) :=
  hs.foldrM (init := φ) fun (h : TSyntax `dl_hyp) acc => do
    match h with
    | `(dl_hyp| ∀ $T:ident $x:ident) => `(dl_fml| ∀ $T $x; ($acc))
    | _ => Solidity.sequentFml #[(h : TSyntax `dl_hyp)] acc

/-- The first `n` layers of a quoted formula as `Logic.lean`'s context
entries: a precondition, an update, a quantified local. -/
def peelHypsC (C : Expr) : Nat → Expr → MetaM (List Expr × Expr)
  | 0, e => pure ([], e)
  | n + 1, e => do
    if e.isAppOfArity ``Solidity.NFml.all 4 || e.isAppOfArity ``Solidity.Surface.Fml.all 4 then
      let (hs, φ) ← peelHypsC C n (e.getArg! 3)
      return (mkApp3 (mkConst ``Solidity.Hyp.all) C (e.getArg! 1) (e.getArg! 2) :: hs, φ)
    let (hs, φ) ← Solidity.peelHyps C 1 e
    let (hs', φ) ← peelHypsC C n φ
    return (hs ++ hs', φ)

/-- The modality at the head of a quoted formula as written, through its
updates. -/
partial def headModality? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Solidity.Surface.Fml.modal 4 then some (e.getArg! 1)
  else if e.isAppOfArity ``Solidity.Surface.Fml.upd 4 then headModality? (e.getArg! 3)
  else none

/-- The sequent `dl{ hs ⟹ φ }` read against `c` as today's: its rule set,
context entries and formula, the modality of the context's updates a
metavariable `φ` fixes when it has one at its head. -/
def readSequent (c : Lean.Term) (arrow : TSyntax `seq_arrow) (hs : Array (TSyntax `dl_hyp))
    (φ : TSyntax `dl_fml) : TermElabM (Expr × List Expr × Expr) := do
  let R := match arrow with
    | `(seq_arrow| ⟹ₖ) => Lean.mkConst ``RuleSet.solkey
    | _ => Lean.mkConst ``RuleSet.all
  let F ← liftMacroM (sequentFmlC hs φ)
  let m ← mkFreshExprMVar (Lean.mkConst ``Modality) (userName := `modality)
  let n ← MonadQuotation.addMacroScope `modality
  let e ← withLocalDeclD n (Lean.mkConst ``Modality) fun x => do
    pure ((← Solidity.elabDlAt c (some (mkIdent n)) F).replaceFVar x m)
  let C := e.getAppArgs[0]!
  let (entries, φ') ← peelHypsC C hs.size e
  if let some m' := headModality? φ' then
    if m'.isConstOf ``Modality.diamond || m'.isConstOf ``Modality.box then
      discard <| isDefEq m m'
  return (R, entries, φ')

/-- Check that the main goal prints as `dl{ hs ⟹ φ }`, read against `c`. -/
def checkSequent (c : Lean.Term) (arrow : TSyntax `seq_arrow) (hs : Array (TSyntax `dl_hyp))
    (φ : TSyntax `dl_fml) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ok ← erasedGoal (← g.getType) fun R gs ψ => Term.TermElabM.run' do
    let (R', hs', ψ') ← readSequent c arrow hs φ
    unless hs'.length == gs.size do return false
    let ok ← isDefEq R R' <&&> (hs'.zip gs.toList).allM (fun (a, b) => isDefEq a b) <&&>
      isDefEq ψ ψ'
    Term.synthesizeSyntheticMVarsNoPostponing
    return ok
  unless ok do
    throwError "show_sequent: the goal is not the sequent written; it is{indentExpr (← g.getType)}"

elab_rules : tactic
  | `(tactic| show_sequent[ $c ]{ $[$hs:dl_hyp],* $a:seq_arrow $φ:dl_fml }) => checkSequent c a hs φ

macro_rules
  | `(tactic| show_sequent!{ $[$hs:dl_hyp],* $a:seq_arrow $φ:dl_fml }) =>
    `(tactic| show_sequent[InContract.contract]{ $[$hs],* $a $φ })

namespace Scoped

scoped macro_rules
  | `(tactic| show sequent!{ $[$hs:dl_hyp],* $a:seq_arrow $φ:dl_fml }) =>
    `(tactic| show_sequent!{ $[$hs],* $a $φ })
  | `(tactic| show sequent[ $c ]{ $[$hs:dl_hyp],* $a:seq_arrow $φ:dl_fml }) =>
    `(tactic| show_sequent[$c]{ $[$hs],* $a $φ })

end Scoped

end Solidity
