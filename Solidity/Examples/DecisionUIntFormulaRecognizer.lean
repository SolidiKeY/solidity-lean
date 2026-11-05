import Solidity.Calculus.DecisionUIntFormulaRecognizer
import Solidity.Examples.DecisionNumericTwoPrefixFormula

/-! # Numeric source membership is not semantic coverage
The existing grammar accepts arithmetic logical combinations and rejects a
symbolic product. Covered Boolean and quantified leaves outside it prevent
interpreting a grammar rejection as Residue or as an unknown verdict.
-/
namespace Solidity.Examples.DecisionUIntFormulaRecognizer
open Solidity.Decide Solidity.Examples.Decision
open Solidity.Examples.DecisionNumericTwoPrefix (input positive)
open Solidity.Examples.DecisionNumericTwoPrefixFormula (right forallEqualsFive)
set_option Elab.async false

def lit (C : Contract) (k : Nat) : Tm C [.val .uint, .val .uint] (.val .uint) :=
  .app0 (.lit (uintOfNat k))
def accepted (C : Contract) : Fml C [.val .uint, .val .uint] :=
  .imp (.eq (input C).val (right C))
    (.and (.eq (input C).val (input C).val) (.not (.eq (lit C 0) (lit C 1))))
def nonlinear (C : Contract) : Fml C [.val .uint, .val .uint] :=
  .eq (.app2 (.binop .mul rfl) (.pvV .here) (.pvV (.there .here))) (lit C 0)
def boolIdentity : Fml Gaps [] :=
  .eq (p := .bool) (.app0 (.lit true)) (.app0 (.lit true))

/-- Constructive positive and negative syntax evidence at the actual two-input context. -/
theorem grammar_controls (C : Contract) :
    (accepted C).QFUIntLinear ∧ ¬ (nonlinear C).QFUIntLinear := by
  exact of_decide_eq_true rfl

/-- Known target/covered leaves can lie outside this restricted syntax grammar. -/
theorem successful_outside_profile :
    ¬ boolIdentity.QFUIntLinear ∧ boolIdentity.qfUIntLinearShape = false ∧
    boolIdentity.inTarget {} = true ∧ boolIdentity.Covered = true ∧
    ¬ positive.QFUIntLinear ∧ positive.qfUIntLinearShape = false ∧
    positive.inTarget {} = true ∧ positive.Covered = true := by
  decide +kernel

/-- info: [true, false, false, false] -/
#guard_msgs in
#eval [(accepted Gaps).qfUIntLinearShape, (nonlinear Gaps).qfUIntLinearShape,
       boolIdentity.qfUIntLinearShape, positive.qfUIntLinearShape]

/-- info: ["proved", "refuted", "unknown"] -/
#guard_msgs in
#eval [verdict boolIdentity, verdict forallEqualsFive, verdict gapHashNegForall]

end Solidity.Examples.DecisionUIntFormulaRecognizer
