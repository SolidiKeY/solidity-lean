import Solidity.Correctness.Lowering.Loops.ReturnFamily

/-!
# The loop-lowering statement

The finish-line candidate for `Solidity.Goals.lowerLoopsCorrect`: the
normal-outcome loop family (`NormalFamilyCorrect`) and the function-level
return family of H497 (`ReturnFamilyCorrect`). Both are family statements;
their link to the actual producer is per sample (`Loops.Correct`).
-/
namespace Solidity.Correctness.Lowering.Loops

/-- Loop lowering is correct on both accepted families. -/
def LowerLoopsCorrect : Prop := NormalFamilyCorrect ∧ ReturnFamilyCorrect

end Solidity.Correctness.Lowering.Loops
