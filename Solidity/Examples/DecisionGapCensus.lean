import Solidity.Examples.DecisionMemory

/-!
# Remaining target controls for the VA1 gap census

These reuse the integrated fixtures and keep their existing verdicts. They do
not define `Fml.Residue` or claim a target-to-coverage theorem. The hidden
parameter is valid over every heap, whereas the global finite witness fallback
only returns countermodels. The struct equations deliberately miss the exact
field/literal schema: reversed sides, or a literal buried in an operator.
-/
namespace Solidity.Examples.DecisionGapCensus
open Solidity.Decide Solidity.Examples.Decision
set_option Elab.async false

/-- A valid repeated read over a given-heap parameter is still a target. -/
theorem hiddenParameter_target : memParamSame.inTarget {} = true := by decide +kernel

/-- The given-heap fallback does not promote one checked heap to global validity. -/
theorem hiddenParameter_unknown : decideGoal memParamSame = .unknown := by rfl

/-- Reversing a field equation does not remove it from the requested target. -/
theorem reversedStruct_target : memStructReversed.inTarget {} = true := by decide +kernel

/-- The exact field/literal classifier retains its existing reversed-side refusal. -/
theorem reversedStruct_unknown : decideGoal memStructReversed = .unknown := by rfl

/-- A literal below addition is admitted syntax, outside the direct literal schema. -/
theorem buriedStruct_target : memStructBuried.inTarget {} = true := by decide +kernel

/-- The existing classifier does not silently treat an operator as a literal. -/
theorem buriedStruct_unknown : decideGoal memStructBuried = .unknown := by rfl

/-- The recognized positive field equation remains an inhabited target control. -/
theorem sameStruct_target : memStructSame.inTarget {} = true := by decide +kernel

/-- The valid hidden-parameter control is not in the current complete fragment. -/
theorem hiddenParameter_notCovered : memParamSame.Covered = false := by decide +kernel

/-- The exact reversed-side refusal is a coverage gap, not a target exclusion. -/
theorem reversedStruct_notCovered : memStructReversed.Covered = false := by decide +kernel

/-- The nonliteral RHS near miss is likewise outside current coverage. -/
theorem buriedStruct_notCovered : memStructBuried.Covered = false := by decide +kernel

end Solidity.Examples.DecisionGapCensus
