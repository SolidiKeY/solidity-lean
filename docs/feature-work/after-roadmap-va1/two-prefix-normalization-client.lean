import Solidity.Calculus.DecisionNumericNormalization
import Solidity.Examples.Decision

namespace Solidity.Examples.VA1TwoPrefixNormalization
open Solidity.Decide Solidity.Examples.Decision

def bothLocals : Tm Gaps [.val .uint, .val .uint] (.val .uint) :=
  .app2 (.binop .add rfl) (.pvV .here) (.pvV (.there .here))
def clientBody : Fml Gaps [.val .uint, .val .uint] :=
  .and .tt (.eq bothLocals (.app0 (.lit (uintOfNat 5))))
def positive : Fml Gaps [] :=
  .all (.user "x") .uint (.eq (.pvV .here) (.pvV .here))
def clientFormula : Fml Gaps [] :=
  .all (.user "x") .uint (.all (.user "y") .uint clientBody)

theorem clientGrammar : clientBody.QFUIntLinear :=
  .and .tt (.eq (.add (.local .here) (.local (.there .here))) (.lit (uintOfNat 5)))

theorem positive_normalization :
    ∃ χ : Fml Gaps [.val .uint, .val .uint],
      (ProgramNormalization.ofFormula? 2048 clientFormula).map (·.formula) =
        some (.all (.user "x") .uint (.all (.user "y") .uint χ)) ∧
      χ.QFUIntLinear ∧ χ.uintQFWeight ≤ clientBody.uintQFWeight :=
  qfUIntTwoPrefix_normalization_sourceFuel (.user "x") (.user "y") clientGrammar
    (by decide +kernel)

/-- The original source work is three visits even though truth reduction
shrinks the returned body; the two quantifiers make the exact threshold five. -/
theorem exact_work_client (budget : Nat) :
    (ProgramNormalization.ofFormula? budget clientFormula).isSome = true ↔ 5 ≤ budget :=
  qfUIntTwoPrefix_normalization_iff_work (.user "x") (.user "y") clientGrammar budget

theorem adjacent_fuel_controls :
    (ProgramNormalization.ofFormula? 4 clientFormula).isSome = false ∧
      (ProgramNormalization.ofFormula? 5 clientFormula).isSome = true := by
  decide +kernel

/-- info: [false, true] -/
#guard_msgs in
#eval [(ProgramNormalization.ofFormula? 4 clientFormula).isSome,
       (ProgramNormalization.ofFormula? 5 clientFormula).isSome]

theorem insufficient_fuel : ProgramNormalization.ofFormula? 1 clientFormula = none := by
  rfl

/-- info: [true, false] -/
#guard_msgs in
#eval [(ProgramNormalization.ofFormula? 2048 clientFormula).isSome,
       (ProgramNormalization.ofFormula? 1 clientFormula).isSome]

/-- info: ["proved", "refuted", "unknown"] -/
#guard_msgs in
#eval [verdict positive, verdict clientFormula, verdict gapHashNegForall]

#print axioms qfUIntTwoPrefix_normalization_iff_work
#print axioms qfUIntTwoPrefix_normalization_sourceFuel
#print axioms positive_normalization
#print axioms exact_work_client
#print axioms adjacent_fuel_controls
#print axioms insufficient_fuel
end Solidity.Examples.VA1TwoPrefixNormalization
