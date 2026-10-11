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
unfolding.  The line is checked on what the goal **prints as**: the goal's
formula with its context folded in front (`Hyps.wrap`) and the line read as
a scoped formula (`cdl[C]{ … }`, the context's entries in front of it as
`sequentFmlC` writes them), both printed by `Calculus/PrintStmt.lean`'s
printer, a block's end not shown, and the two lines compared, after the
line's entries are counted against the goal's (an entry folded into the
formula, `a → φ` for the entry `a`, prints the same but is not the line).
So the line is written as the goal prints, without the `}` of a block's
end, and a hidden binder is no entry.

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

/-- The sequent's formula, written: `a → …` for a precondition, `{U} …`
for an update, `∀ T x; …` for a quantified local. -/
def sequentFmlC (hs : Array (TSyntax `dl_hyp)) (φ : TSyntax `dl_fml) :
    MacroM (TSyntax `dl_fml) :=
  hs.foldrM (init := φ) fun (h : TSyntax `dl_hyp) acc => do
    match h with
    | `(dl_hyp| ∀ $T:ident $x:ident) => `(dl_fml| ∀ $T $x; ($acc))
    | _ => Solidity.sequentFml #[(h : TSyntax `dl_hyp)] acc

/-- The line a scoped formula `e : Fml C Γ₀` prints as, a block's end not
shown. -/
def fmlLine (e : Expr) : MetaM String := do
  let φ ← Delab.withPrinter e false (Delab.ppFmlS [] e)
  return (← PrettyPrinter.ppCategory `dl_fml φ).pretty 100000

/-- Check that the main goal prints as `dl{ hs ⟹ φ }`, read against `c`. -/
def checkSequent (c : Lean.Term) (arrow : TSyntax `seq_arrow) (hs : Array (TSyntax `dl_hyp))
    (φ : TSyntax `dl_fml) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``Proves 6 do throwError "show_sequent: not a scoped goal{indentExpr ty}"
  let R := match arrow with
    | `(seq_arrow| ⟹ₖ) => ``RuleSet.solkey
    | _ => ``RuleSet.all
  -- The context's entries as the goal prints them (a hidden binder, an
  -- empty update are none): the line must write as many.
  let n ← Delab.withPrinter ty false do
    let (r, gs, _) ← Delab.hypsPartsS (ty.getArg! 0) (ty.getArg! 4)
    return gs.size + (if r.isSome then 1 else 0)
  unless n == hs.size do
    throwError "show_sequent: the goal has {n} context entries, the line {hs.size}; it is{indentExpr (← g.getType)}"
  let goal ← fmlLine (← mkAppM ``Hyps.wrap #[ty.getArg! 4, ty.getArg! 5])
  let line ← Term.TermElabM.run' do
    let F ← liftMacroM (sequentFmlC hs φ)
    let e ← elabCdlAt c none F (useAll := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    fmlLine (← instantiateMVars e)
  unless (← whnf (ty.getArg! 1)).isConstOf R && goal == line do
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
