import Solidity.Calculus.Completeness

/-!
# One rule per statement

`Taclet` is a `Prop`, so "one rule per statement" is a statement about
premises: two derivations of `s` leave the same premise
(`Taclet.premise_unique`), and that premise is the one `Stmt.step` fires
(`Taclet.eq_step`).  With `Stmt.complete`, every statement has exactly one
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

/-- Case on a part whose constructor `Stmt.step` reads: a variable a side
condition speaks of, or a storage or memory location. -/
elab "cases_part" : tactic => withMainContext do
  let g ← getMainGoal
  let lctx ← getLCtx
  let parts := [``Val, ``SPath, ``Loc, ``MPath, ``MLoc, ``BinOp]
  let isPart (e : Expr) : MetaM Bool := do
    let t ← whnfR (← instantiateMVars (← inferType e))
    return parts.any t.isAppOf
  for d in lctx do
    if d.isImplementationDetail then continue
    let some (_, lhs, _) := (← instantiateMVars d.type).eq? | continue
    unless (``BinOp.shortCircuits :: sidePreds).any lhs.isAppOf do continue
    for fv in (Lean.collectFVars {} lhs).fvarIds do
      if ← isPart (.fvar fv) then
        let gs ← g.cases fv
        replaceMainGoal (gs.map (·.mvarId)).toList
        return
  for d in lctx do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOf ``Loc || t.isAppOf ``MLoc then
      let gs ← g.cases d.fvarId
      replaceMainGoal (gs.map (·.mvarId)).toList
      return
  throwError "cases_part: no part to case on"

/-- Case on a memory source or an index kind `Stmt.step` still matches on. -/
elab "cases_extra" : tactic => withMainContext do
  let g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOf ``MSrc || t.isAppOf ``IndexTy then
      let gs ← g.cases d.fvarId
      replaceMainGoal (gs.map (·.mvarId)).toList
      return
  throwError "cases_extra: nothing to case on"

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

/-- **At most one rule per statement**: two derivations of `s` leave the same
premise.  `alice.age = 10;` is `storageFieldWriteSave` and nothing else,
`people[i].age = 10;` is `storageFieldWrite_unfold_leftFst` and nothing else. -/
theorem Taclet.premise_unique {s : Stmt C} {p p' : Premise C} (d : Taclet C k m s p)
    (d' : Taclet C k m s p') : p = p' := by
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
