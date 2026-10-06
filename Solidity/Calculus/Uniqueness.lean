import Solidity.Calculus.Completeness

/-!
# One rule per statement

`Taclet` is a `Prop`, so "one rule per statement" is a statement about
premises: two derivations of `s` leave the same premise
(`Rule.premise_unique`), and that premise is the one `Stmt.step` fires
(`Taclet.eq_step`, `LeanTaclet.eq_step`).  With `Stmt.complete`, every statement has exactly one
rule.

What makes it hold is the side conditions of `Rules.lean`: a constructor's
schema variables say what they are (`nsp` is not simple, `sp` is), and its
hidden hypotheses say what `Stmt.step` knows of the parts when it fires the
rule (`RuleSyntax.sideConds`).  Where solkey leaves two taclets open on one
statement and its strategy picks, the kernel's side condition leaves only
the one `Stmt.step` picks:

* an unfold or capture rule takes a part that is not simple, a terminal rule
  one that is (`if (b) …` splits, `if (b && c) …` captures);
* a conditional written to storage or memory is lowered, never captured
  (`Val.notTernary`: `sp.f = c ? a : b;`);
* a copy between two storage members unfolds its target first
  (`Loc.isTarget` on the source unfolds: `folks[1].account = folks[2].account;`);
* a memory reference is written as it is only from a bindable source
  (`MPath.isBindable`), and a memory target unfolds first.

The proof reads each derivation's parts down to the constructors
`Stmt.step` branches on (`cases_part`, `cases_extra`), settles the side
conditions that compute (`settle_side`), and then the dispatcher computes the
derivation's own premise.
-/

namespace Solidity

variable {C : Contract} {k : Nat} {m : Modality}

section Tactics
open Lean Elab Tactic Meta

/-- Settle the side conditions that compute: drop the true ones, close the
goal on a false one (and on an operator applied at a type it does not
accept). -/
elab "settle_side" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let mut g := g
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | continue
    unless (``BinOp.accepts :: ``BinOp.shortCircuits :: sidePreds).any lhs.isAppOf do continue
    let v ← whnfD lhs
    let r ← whnfD rhs
    unless v.isConstOf ``Bool.true || v.isConstOf ``Bool.false do continue
    if v == r then
      g ← g.tryClear d.fvarId
    else
      let g' ← g.replaceLocalDeclDefEq d.fvarId (← mkEq v r)
      g'.contradiction
      replaceMainGoal []
      return
  replaceMainGoal [g]

/-- Case on the local `fv` of the main goal. -/
def casesLocal (fv : FVarId) : TacticM Unit := do
  let gs ← (← getMainGoal).cases fv
  replaceMainGoal (gs.map (·.mvarId)).toList

/-- Case on the first local of the main goal whose type is one of `heads`;
whether there was one. -/
def casesFirstLocal (heads : List Lean.Name) : TacticM Bool := withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if heads.any t.isAppOf then
      casesLocal d.fvarId
      return true
  return false

/-- Case on a part whose constructor `Stmt.step` reads: a variable a side
condition speaks of, or a storage or memory location. -/
elab "cases_part" : tactic => withMainContext do
  let parts := [``Val, ``SPath, ``Loc, ``MPath, ``MLoc, ``BinOp]
  let isPart (e : Expr) : MetaM Bool := do
    let t ← whnfR (← instantiateMVars (← inferType e))
    return parts.any t.isAppOf
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, lhs, _) := (← instantiateMVars d.type).eq? | continue
    unless (``BinOp.shortCircuits :: sidePreds).any lhs.isAppOf do continue
    for fv in (Lean.collectFVars {} lhs).fvarIds do
      if ← isPart (.fvar fv) then
        casesLocal fv
        return
  unless ← casesFirstLocal [``Loc, ``MLoc] do throwError "cases_part: no part to case on"

/-- Case on a memory source or an index kind `Stmt.step` still matches on. -/
elab "cases_extra" : tactic => do
  unless ← casesFirstLocal [``MSrc, ``IndexTy] do throwError "cases_extra: nothing to case on"

end Tactics

set_option maxHeartbeats 4000000 in
/-- **Every derivation is `Stmt.step`'s**: whatever rule derives `s`, its
premise is the one the dispatcher fires.  `x = people[i].age;` has only
`storageFieldRead_unfold_rightFst` (the receiver `people[i]` is not simple,
so `storageFieldReadFind` does not apply), and `if (b) { … } else { … }`,
`b` a local, only `ifElseSplit`. -/
theorem Taclet.eq_step {s : Stmt C} {p : Premise C} (d : Taclet C k m s p) :
    p = (s.step k m).premise := by
  cases d <;> (try cases ‹Hole _ _›) <;> (try cases ‹MHole _ _›) <;> (try cases ‹VHole _ _›)
  -- a call: whether an argument is not ready picks the rule
  case functionBodyExpand h hr =>
    simp only [Stmt.step, callStep]
    split <;> simp_all <;> subst_vars
    split <;> simp_all
  case internalCallExpand h hr =>
    simp only [Stmt.step, callStep]
    split <;> simp_all <;> subst_vars
    split <;> simp_all
  all_goals settle_side
  all_goals repeat' (cases_part <;> settle_side)
  all_goals (try rfl)
  all_goals repeat' (cases_extra <;> settle_side)
  all_goals (try rfl)
  -- an array's element type picks between two rules (`storagePopSave`,
  -- `storagePopSaveMappingElement`): the dispatcher's `if` on it is settled
  -- by the side condition
  all_goals first
    | (simp only [Stmt.step, rebindStep, popStep, pushStep, Hole.readStep, Hole.fill]
       repeat' split
       all_goals first
         | rfl
         | (simp_all; done)
         | (simp_all [SPath.elemMapping, SPath.elemPrim, Ty.elemIsMapping, Ty.elemIsPrim]; done)
         | exact absurd rfl ‹¬ _›
       done)
    | skip
  -- a conditional written to a member or an entry is lowered whether or not
  -- its receiver is simple: both branches of the dispatcher agree
  all_goals
    simp only [Stmt.step, assignStep, VHole.lower, VHole.step, ternaryStep, VHole.fill]
    repeat' split
    all_goals rfl

/-- The rules solkey lacks are `Stmt.step`'s too: a call with an argument
that is not ready captures it, and a `try` under the diamond closes. -/
theorem LeanTaclet.eq_step {s : Stmt C} {p : Premise C} (d : LeanTaclet C k m s p) :
    p = (s.step k m).premise := by
  cases d with
  | functionCallArgCapture h =>
    simp only [Stmt.step, callStep]
    split <;> simp_all <;> subst_vars <;> rfl
  | tryCallDiamond => rfl
  | transferDiamond => rfl

theorem Rule.eq_step {s : Stmt C} {p : Premise C} (d : Rule C k m s p) :
    p = (s.step k m).premise := by
  cases d with
  | key d => exact d.eq_step
  | lean d => exact d.eq_step

/-- **At most one rule per statement**: two derivations of `s` leave the same
premise.  `alice.age = 10;` is `storageFieldWriteSave` and nothing else,
`people[i].age = 10;` is `storageFieldWrite_unfold_leftFst` and nothing else. -/
theorem Rule.premise_unique {s : Stmt C} {p p' : Premise C} (d : Rule C k m s p)
    (d' : Rule C k m s p') : p = p' := by
  rw [d.eq_step, d'.eq_step]

/-! `if (b) { } else { }` with `b` a local has one rule, `ifElseSplit`:
`ifElseUnfold` asks for a condition that is not simple, and its side
condition cannot be proved. -/

/--
error: could not synthesize default value for parameter 'hnse' using tactics
---
error: the rule's side condition does not hold: `Stmt.step` fires another rule here
C : Contract
k : Nat
m : Modality
c : Simple C PrimTy.bool
⊢ (Val.simple c).isSimple = false
-/
#guard_msgs in
example (c : Simple C .bool) : ∃ p, Taclet C k m (.ite (.simple c) [] []) p :=
  ⟨_, .ifElseUnfold⟩

end Solidity
