import Solidity.Correctness.Lowering.Loops.ReturnFamily

/-!
# The loop-lowering statement

The e1-loops family theorem's statement: the normal-outcome loop family
(`NormalFamilyCorrect`) and the callee-body-pass return family of H497
(`ReturnFamilyCorrect`). Both are family statements; their link to the actual
producer is per sample here (`Loops.Correct`). Per H503(4) the universal link is
e2b-loops-producer's: a relational `LowersTo` spec that `lowerLoops` satisfies,
composed with this statement into `Solidity.Correctness.Lowering.lowerLoops_correct`
(the finish-line component `Solidity.Goals.lowerLoopsCorrect`). This lane does
not state or prove that goal.
-/
namespace Solidity.Correctness.Lowering.Loops

/-- Loop lowering is correct on both accepted families. -/
def LoopFamilyCorrect : Prop := NormalFamilyCorrect ∧ ReturnFamilyCorrect

end Solidity.Correctness.Lowering.Loops
