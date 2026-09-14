import Solidity.Update.Eval
import Solidity.Wp.Verdict

/-!
# Reading a rule's goals as a weakest precondition

A KeY taclet rewrites a sequent, and the sequent it rewrites is a dynamic-logic
judgment.  Read backwards — as a weakest precondition — each goal of a taclet
applied to `⟨stmt; rest⟩post` says

    guard  →  {update} ⟨residual ++ rest⟩ post

and the taclet says the conjunction of its goals, over those whose modality
applies.  `StepEffect.wp` is that conjunction, and `RuleGoal.check` is one
conjunct, in the verdict shape `SolidityJudgment.check` already uses: a `stuck`
run validates nothing, a `revert` validates a box judgment and refutes a
diamond one.

## Why the lemmas are per combinator

The bridge to the interpreter is `checkResult sm post (goalsExec … >>= execBlock rest)`
— "run the rule's update, then the rest, then read the verdict".  Turning the
conjunction into that requires knowing that the goals are *exhaustive*: that
whenever no goal's update fires, some goal has already accounted for the revert.
That is not true of an arbitrary goal list — `[guard false → prog]` says nothing
and reverts — but it is true of every shape `Rules.lean` actually builds, and
those are four.  So the lemmas below are stated per combinator rather than by
induction on goals, which is both provable and more informative: they say
exactly which shapes are exhaustive.

`Rules.assertGoals` is deliberately absent from the list.  It is *not*
exhaustive, and that is KeY's own reading: its violated branch is an obligation
to prove the condition, not a revert, so under the box modality the rule is
strictly stronger than the statement it describes.  `assertSimple_box_gap`
(`Update/SolcDelta.lean`) is the witness.
-/

namespace Solidity
namespace Update

open Semantics Wp Rules

/-- The verdict one goal contributes to `⟨sm, stmt :: rest⟩post` at `s`. -/
def RuleGoal.check (g : RuleGoal) (sm : SolidityModality) (rest : Block)
    (post : WrappedExpr) (s : State) : Bool :=
  match Guard.eval g.guard s with
  | .error .stuck => false
  | .error .revert => decide (sm = SolidityModality.box)
  | .ok false => true
  | .ok true =>
      match g.residual with
      | RuleResidual.prog upd b =>
          match UpdTerm.toUpd upd s with
          | .ok s' => checkResult sm post (execBlock s' (b ++ rest))
          | .error .revert => decide (sm = SolidityModality.box)
          | .error .stuck => false
      | RuleResidual.reverting => decide (sm = SolidityModality.box)
      | RuleResidual.obligation upd φ =>
          match UpdTerm.toUpd upd s with
          | .ok s' =>
              match SideFormula.eval s' φ with
              | .ok b => b
              | .error _ => false
          | .error .revert => decide (sm = SolidityModality.box)
          | .error .stuck => false

/-- The rule's weakest precondition: every goal whose modality applies. -/
def StepEffect.wp (gs : List RuleGoal) (sm : SolidityModality) (rest : Block)
    (post : WrappedExpr) (s : State) : Prop :=
  ((gs.filter fun g => sm.appliesCaseMode g.mode).all
    fun g => RuleGoal.check g sm rest post s) = true

instance (gs : List RuleGoal) (sm : SolidityModality) (rest : Block)
    (post : WrappedExpr) (s : State) :
    Decidable (StepEffect.wp gs sm rest post s) :=
  inferInstanceAs (Decidable (_ = true))

/-! ## The shapes that are exhaustive -/

/-- An unguarded terminal rule: `{u}⟨rest⟩post`. -/
theorem wp_terminalGoal (sm : SolidityModality) (upd : UpdTerm) (rest : Block)
    (post : WrappedExpr) (s : State) :
    StepEffect.wp (terminalGoal upd) sm rest post s ↔
      checkResult sm post (goalsExec sm (terminalGoal upd) s >>=
        fun t => execBlock t rest) = true := by
  have happ : sm.appliesCaseMode CaseMode.both = true := by
    cases sm <;> rfl
  simp only [terminalGoal, StepEffect.wp, goalsExec, RuleGoal.check,
    List.filter, happ, List.all_cons, List.all_nil, Bool.and_true,
    decide_eq_true_eq]
  cases hu : UpdTerm.toUpd upd s with
  | ok t => simp [Guard.eval, runPremises, SideFormula.eval, hu, bind, Except.bind,
      List.nil_append]
  | error e =>
      cases e <;>
        simp [Guard.eval, runPremises, SideFormula.eval, hu, bind, Except.bind,
          checkResult, decide_eq_true_eq]

/-- KeY's guarded pair.  It *is* exhaustive: the two goals share a guard and
partition on its truth, so whichever way the guard falls one of them speaks. -/
theorem wp_splitGoals (sm : SolidityModality) (φ : SideFormula)
    (prem : List Premise) (upd : UpdTerm) (rest : Block) (post : WrappedExpr)
    (s : State) :
    StepEffect.wp (splitGoals φ prem upd) sm rest post s ↔
      checkResult sm post (goalsExec sm (splitGoals φ prem upd) s >>=
        fun t => execBlock t rest) = true := by
  have happ : sm.appliesCaseMode CaseMode.both = true := by
    cases sm <;> rfl
  have hneg : ∀ t : State, Guard.eval { premises := prem, formula := φ.neg } t =
      (Guard.eval { premises := prem, formula := φ } t).map not := by
    intro t
    simp only [Guard.eval, SideFormula.eval, bind, Except.bind, Except.map]
    cases runPremises prem t <;> rfl
  simp only [splitGoals, StepEffect.wp, goalsExec, RuleGoal.check,
    List.filter, happ, List.all_cons, List.all_nil, Bool.and_true,
    decide_eq_true_eq, hneg, Except.map]
  cases hg : Guard.eval { premises := prem, formula := φ } s with
  | error e =>
      cases e <;> simp [bind, Except.bind, checkResult, decide_eq_true_eq]
  | ok b =>
      cases b with
      | false => simp [bind, Except.bind, checkResult, decide_eq_true_eq]
      | true =>
          cases hu : UpdTerm.toUpd upd s with
          | ok t => simp [bind, Except.bind, hu, List.nil_append]
          | error e =>
              cases e <;>
                simp [bind, Except.bind, hu, checkResult, decide_eq_true_eq]

/-- `revert();`: two constant goals, one per modality, and the rule's own
`mode` picks.  Neither produces a state, so `goalsExec` falls through to its
`revert` — which is the statement's meaning. -/
theorem wp_revertGoals (sm : SolidityModality) (rest : Block)
    (post : WrappedExpr) (s : State) :
    StepEffect.wp revertGoals sm rest post s ↔
      checkResult sm post (goalsExec sm revertGoals s >>=
        fun t => execBlock t rest) = true := by
  have hrev : goalsExec sm revertGoals s = .error .revert := by
    cases sm <;> rfl
  rw [hrev]
  cases sm <;>
    simp only [revertGoals, obligation, StepEffect.wp, RuleGoal.check,
      SolidityModality.appliesCaseMode, CaseMode.applies, List.filter,
      Guard.eval, runPremises, SideFormula.eval, bind, Except.bind, Except.map,
      pure, Except.pure, List.all_cons, List.all_nil, Bool.and_true,
      Bool.false_and, UpdTerm.toUpd, UpdTerm.toPar, List.flatMap,
      Upd.Par.toUpd, Upd.Par.apply, Upd.Par.writers, checkResult,
      decide_eq_true_eq] <;>
    simp

end Update
end Solidity
