import Solidity.Calculus.DecisionUIntShape
import Solidity.Examples.DecisionUIntBridge

/-! # Executable intrinsic grammar controls
Rejection means only that the term is outside UIntLinear. It does not claim
unknown, invalidity, lack of coverage or failure of source admission.
-/
namespace Solidity.Examples.DecisionUIntShape
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
open Solidity.Examples.DecisionUIntBridge
set_option Elab.async false

def two : Tm Bank [.val .uint] (.val .uint) := .app0 (.lit (uintOfNat 2))
def left : Tm Bank [.val .uint] (.val .uint) := .app2 (.binop .mul rfl) two current
def right : Tm Bank [.val .uint] (.val .uint) := .app2 (.binop .mul rfl) current two
def nested : Tm Bank [.val .uint] (.val .uint) :=
  .app2 (.binop .add rfl) left (.app2 (.binop .sub rfl) right two)
def foldedCoefficient : Tm Bank [.val .uint] (.val .uint) :=
  .app2 (.binop .mul rfl) (.app2 (.binop .add rfl) two two) current

theorem nested_accepted : nested.uintLinearShape = true := by decide +kernel

theorem existing_grammar_decidable : nested.UIntLinear := by decide +kernel

theorem nonlinear_rejected : nonlinear.uintLinearShape = false := by decide +kernel

theorem nonlinear_grammar_decidable : ¬ nonlinear.UIntLinear := by decide +kernel

theorem folded_coefficient_rejected : foldedCoefficient.uintLinearShape = false := by decide +kernel

/-- Both literal operand orders are accepted by the exact existing grammar. -/
theorem literal_orders : left.UIntLinear ∧ right.UIntLinear := by decide +kernel

/-- Syntactic acceptance connects to actual target coverage and certificates. -/
theorem nested_source_covered : (primitivePrefixEq (.user "x") nested nested).Covered = true :=
  uintShapePrefix_Covered _ _ _ nested_accepted nested_accepted (by decide +kernel)

theorem partial_source_certified :
    (decideGoal partialLeaf = .proved ∧ Fml.ValidH partialLeaf) ∨
      ∃ σ : State Bank [], decideGoal partialLeaf = .refuted σ ∧ ¬ Fml.holdsH σ partialLeaf :=
  uintShapePrefix_certified (.user "x") decrement1 decrement2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Partial arithmetic still has the original inhabited negative control. -/
theorem partial_countermodel_retained : ¬ holds (State.init Bank) partialLeaf :=
  partialLeaf_countermodel

end Solidity.Examples.DecisionUIntShape
