import Solidity.Tools.Goal

/-! Finish-line component 3: `Solidity.Correctness.Lowering.lowerLoops_correct`
(owner: e1-loops), and the pa-lowering study target that reuses its statement. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Correctness.Lowering.lowerLoops_correct "e1-loops"]
def lowerLoopsCorrect : Prop := Unstated

@[goal Solidity.Correctness.Lowering.lowerLoops_correct "pa-lowering" ← lowerLoopsCorrect]
def loweringStudyTarget : Prop := lowerLoopsCorrect

end Solidity.Goals
