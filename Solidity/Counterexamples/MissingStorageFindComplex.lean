import Solidity.Calculus.Uniqueness

/-!
# Dropping `storageFieldReadUnfoldRightFst` loses a first step

Why the read-unfold family needs its *complex-path* member, and not only the
simple-field one.  `reducedStepCases` is `Rules.stepCases` with
`storageFieldReadUnfoldRightFst` removed, and `stmt` is a deep field read
(`alice.account.balance`) that the full table covers (`stmt_covered`,
`original_first_step`).

Against that reduced table the statement has no first step at all
(`reduced_no_first_step`), hence no `ReducedRuleStep` (`reduced_no_rule_step`),
hence the completeness statement of `Calculus/Completeness.lean` fails outright
(`reduced_not_complete_against_original_first_step`).  So the rule is not
redundant with the simple-field read: a path that must itself be unfolded
before the read has no other rule to fall through to.
-/

namespace Solidity

open Rules

namespace Counterexamples
namespace MissingStorageFindComplex

def keepRule (step : StepCase) : Bool :=
  match step.rule with
  | RuleName.storageFieldReadUnfoldRightFst => false
  | _ => true

def reducedStepCases (stmt : Stmt) : List StepCase :=
  (Rules.concreteStepCases stmt).filter keepRule

inductive ReducedRuleStep (sm : SolidityModality) :
    Stmt -> Prop -> Block -> Prop where
  | ofStepCase {lhs : Stmt} {step : StepCase} {cond : Prop}
      {block : Block}
      (hfirst :
        FirstStepCase sm lhs (reducedStepCases lhs) step cond block) :
      ReducedRuleStep sm lhs cond block

def ReducedFirstStep (sm : SolidityModality)
    (lhs : Stmt) : Prop :=
  ∃ step cond block,
    FirstStepCase sm lhs (reducedStepCases lhs) step cond block

def alice : PlaceExpr :=
  splace!{ alice }

def account : PlaceExpr :=
  splace!{ alice.account }

def balance : PlaceExpr :=
  splace!{ alice.account.balance }

def target : PlaceExpr :=
  svar!{ stack int target }

def stmt : Stmt :=
  Stmt.assign target sexpr!{ alice.account.balance }

theorem stmt_covered : Rules.ruleApplies .box stmt := by
  refine ⟨.storageFieldReadUnfoldRightFst, by decide, ?_, ?_⟩ <;>
    simp [Rules.ruleEffect, Rules.assignEffect, stmt, target,
      SoliditySyntax.fieldExpr, SoliditySyntax.rootExpr,
      SoliditySyntax.varExpr, SoliditySyntax.varPlace,
      SoliditySyntax.typedKind, SoliditySyntax.typedVarTy,
      SoliditySyntax.fieldTy, Rules.isComplex, Typed.WrappedExpr.complex,
      Typed.WrappedExpr.simple, Typed.WrappedExpr.kind, PlaceExpr.var,
      PlaceExpr.kind, CaseMode.applies]

theorem original_first_step :
    ∃ schema cond block,
      FirstStepCase (.ofModality .box) stmt Rules.stepCases schema cond block := by
  exact CompletenessAux.firstStepCase_of_ruleApplies .box stmt
    stmt_covered

theorem reduced_no_first_step : ¬ ReducedFirstStep (.ofModality .box) stmt := by
  intro h
  rcases h with ⟨step, cond, block, hfirst⟩
  have hmemReduced := FirstStepCase.mem hfirst
  have hfilter : step ∈ Rules.rules ∧ keepRule step = true := by
    simpa [reducedStepCases, Rules.concreteStepCases, Rules.stepCases]
      using (List.mem_filter.mp hmemReduced)
  have hne : step.rule ≠ RuleName.storageFieldReadUnfoldRightFst := by
    intro heq
    simp [keepRule, heq] at hfilter
  have hrmem : step.rule ∈ Rules.ruleNames := by
    obtain ⟨rule, hrule, rfl⟩ := Rules.mem_stepCases_iff.mp hfilter.1
    exact hrule
  have hsapp : StepApplicable .box stmt step := by
    refine ⟨?_, FirstStepCase.effect_cond_holds hfirst⟩
    simpa [CompletenessAux.appliesCaseMode_of_ofModality]
      using FirstStepCase.mode_holds hfirst
  rw [UniquenessAux.mem_rules_eq_stepCase hfilter.1] at hsapp
  have hmissing : StepApplicable .box stmt
      (Rules.stepCase .storageFieldReadUnfoldRightFst) := by
    simp [StepApplicable, Rules.stepCase,
      Rules.ruleEffect, Rules.assignEffect, stmt, target,
      SoliditySyntax.fieldExpr, SoliditySyntax.rootExpr,
      SoliditySyntax.varExpr, SoliditySyntax.varPlace,
      SoliditySyntax.typedKind, SoliditySyntax.typedVarTy,
      SoliditySyntax.fieldTy, Rules.isComplex, Typed.WrappedExpr.complex,
      Typed.WrappedExpr.simple, Typed.WrappedExpr.kind, PlaceExpr.var,
      PlaceExpr.kind, CaseMode.applies]
  exact UniquenessAux.ruleName_exclusive hrmem (by decide) hne
    hsapp hmissing

theorem reduced_no_rule_step :
    ¬ ∃ cond rhs,
      cond ∧ ReducedRuleStep (.ofModality .box) stmt cond rhs := by
  intro h
  rcases h with ⟨_cond, _rhs, _hholds, hstep⟩
  apply reduced_no_first_step
  cases hstep with
  | ofStepCase hfirst =>
      exact ⟨_, _, _, hfirst⟩

theorem reduced_not_complete_against_original_first_step :
    ¬ (∀ lhs : Stmt,
      (∃ schema cond block,
        FirstStepCase (.ofModality .box) lhs Rules.stepCases schema cond block) ->
        ∃ cond rhs,
          cond ∧ ReducedRuleStep (.ofModality .box) lhs cond rhs) := by
  intro hcomplete
  exact reduced_no_rule_step (hcomplete stmt original_first_step)

end MissingStorageFindComplex
end Counterexamples

end Solidity
