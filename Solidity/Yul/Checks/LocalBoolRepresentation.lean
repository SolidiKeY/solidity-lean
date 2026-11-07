import Solidity.Yul.LocalBoolRepresentation

namespace Solidity.Yul.Checks.LocalBoolRepresentation
def env : Solidity.Source.Env := ⟨[]⟩
def cleanTrue : LocalValue env .bool := .clean (.bool true)
def cleanFalse : LocalValue env .bool := .clean (.bool false)
def raw (n : Nat) : LocalValue env .bool :=
  .scalar (LocalOperations.boolShape env) (Solidity.Yul.word n)
def expr : Solidity.Source.RExpr env [.bool] .bool :=
  .assign (.local .here) (.unary .not (.local .here))
def supported : LocalBoolExpr.Supported env [.bool] expr :=
  .assign .here (.not (.local .here))
def witness : Nonempty (LocalBoolExpr.Supported env [.bool] expr) := ⟨supported⟩
def concrete (fuel : Nat) (one two : LocalState env [.bool])
    (related : Solidity.Yul.LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalBoolRepresentation.expression env [.bool] expr supported fuel one two related

theorem oneRelated : Solidity.Yul.LocalBoolRepresentation.Value Solidity.Yul.Checks.LocalBoolRepresentation.env Solidity.Yul.Checks.LocalBoolRepresentation.cleanTrue (Solidity.Yul.Checks.LocalBoolRepresentation.raw 1) := by

  exact .boolean rfl

theorem zeroRelated : Solidity.Yul.LocalBoolRepresentation.Value Solidity.Yul.Checks.LocalBoolRepresentation.env Solidity.Yul.Checks.LocalBoolRepresentation.cleanFalse (Solidity.Yul.Checks.LocalBoolRepresentation.raw 0) := by

  exact .boolean rfl

theorem dirtyRefused : ¬ Solidity.Yul.LocalBoolRepresentation.Value Solidity.Yul.Checks.LocalBoolRepresentation.env Solidity.Yul.Checks.LocalBoolRepresentation.cleanTrue (Solidity.Yul.Checks.LocalBoolRepresentation.raw 2) := by

  intro related
  have words := Solidity.Yul.LocalBoolRepresentation.value_word _ _ _ related
  exact (by decide : Solidity.Yul.LocalBoolRepresentation.word Solidity.Yul.Checks.LocalBoolRepresentation.cleanTrue ≠ Solidity.Yul.LocalBoolRepresentation.word (Solidity.Yul.Checks.LocalBoolRepresentation.raw 2)) words

theorem projectionDiffers : (Solidity.Yul.Checks.LocalBoolRepresentation.cleanTrue.clean?).isSome = true ∧ ((Solidity.Yul.Checks.LocalBoolRepresentation.raw 1).clean?).isSome = false := by

  decide

theorem dirtyTruth : Solidity.Yul.LocalBoolControl.truth Solidity.Yul.Checks.LocalBoolRepresentation.cleanTrue = Solidity.Yul.LocalBoolControl.truth (Solidity.Yul.Checks.LocalBoolRepresentation.raw 2) := by

  rfl

theorem combination : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolRepresentation.env), Solidity.Yul.LocalBoolExpr.eval Solidity.Yul.Checks.LocalBoolRepresentation.supported 3 (((Solidity.Yul.Checks.LocalBoolRepresentation.raw 1,()),world)) = (.ok Solidity.Yul.Checks.LocalBoolRepresentation.cleanFalse,((Solidity.Yul.Checks.LocalBoolRepresentation.cleanFalse,()),world)) := by

  intro world; rfl

theorem haltDistinction : ¬ Solidity.Yul.LocalBoolRepresentation.Outcome Solidity.Yul.Checks.LocalBoolRepresentation.env (.error .timeout) (.error (.revert [])) := by

  intro related
  cases related

#print axioms Solidity.Yul.LocalBoolRepresentation.value_word
#print axioms Solidity.Yul.LocalBoolRepresentation.not_congr
#print axioms Solidity.Yul.LocalBoolRepresentation.read
#print axioms Solidity.Yul.LocalBoolRepresentation.write
#print axioms Solidity.Yul.LocalBoolRepresentation.observe
#print axioms Solidity.Yul.LocalBoolRepresentation.truth_congr
#print axioms Solidity.Yul.LocalBoolRepresentation.expression
#print axioms Solidity.Yul.LocalBoolRepresentation.outcome_cases
#print axioms oneRelated
#print axioms zeroRelated
#print axioms dirtyRefused
#print axioms projectionDiffers
#print axioms dirtyTruth
#print axioms combination
#print axioms haltDistinction

end Solidity.Yul.Checks.LocalBoolRepresentation
