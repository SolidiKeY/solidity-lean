import Solidity.Examples.DecisionMemory
import Solidity.Calculus.DecisionMemoryCoverage

/-!
# Remaining target controls for the VA1 gap census

These reuse the integrated fixtures and certify the assigned reversed-field improvement. They do
not define `Fml.Residue` or claim a target-to-coverage theorem. The hidden
parameter now has an all-heap source certificate, while the finite candidate
checker remains a countermodel-only component. The reversed equation now reaches a certified fallback; a literal buried in
an operator remains outside the direct field/literal schema.
-/
namespace Solidity.Examples.DecisionGapCensus
open Solidity.Decide Solidity.Examples.Decision
set_option Elab.async false

/-- A valid repeated read over a given-heap parameter is still a target. -/
theorem hiddenParameter_target : memParamSame.inTarget {} = true := by decide +kernel

/-- Global validity comes from the exact all-heap source certificate. -/
theorem hiddenParameter_proved : decideGoal memParamSame = .proved := memParamSame_proved

/-- Reversing a field equation does not remove it from the requested target. -/
theorem reversedStruct_target : memStructReversed.inTarget {} = true := by decide +kernel

/-- The actual source parser supplies the typed witness, without choice. -/
def reversedWitness : ResidueReason.ReversedFreshField memStructReversed :=
  (ResidueReason.reversedFreshField? memStructReversed).get (by decide +kernel)

/-- The global route returns the original child-heap state before parent allocation. -/
theorem reversedStruct_exact_state :
    decideGoal memStructReversed = .refuted gapMemStruct_state := by rfl

/-- The actual returned state refutes the unchanged hash reading. -/
theorem reversedStruct_returned_refutesH : ¬ Fml.holdsH gapMemStruct_state memStructReversed :=
  decideGoal_refutes reversedStruct_exact_state

/-- A literal below addition is admitted syntax, outside the direct literal schema. -/
theorem buriedStruct_target : memStructBuried.inTarget {} = true := by decide +kernel

/-- The existing classifier does not silently treat an operator as a literal. -/
theorem buriedStruct_unknown : decideGoal memStructBuried = .unknown := by rfl

/-- The recognized positive field equation remains an inhabited target control. -/
theorem sameStruct_target : memStructSame.inTarget {} = true := by decide +kernel

/-- The valid hidden-parameter source is now in the complete memory fragment. -/
theorem hiddenParameter_covered : memParamSame.Covered = true := memParamSame_covered

/-- The exact reversed-side source now has a certified coverage route. -/
theorem reversedStruct_covered : memStructReversed.Covered = true := reversedWitness.covered

/-- The nonliteral RHS near miss is likewise outside current coverage. -/
theorem buriedStruct_notCovered : memStructBuried.Covered = false := by decide +kernel

end Solidity.Examples.DecisionGapCensus
