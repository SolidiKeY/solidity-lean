import Solidity.Goals.Loops

namespace Solidity.Goals

/--
info: unstated Solidity.Goals.lowerLoopsCorrect ← Solidity.Correctness.Lowering.lowerLoops_correct plan e1-loops
-/
#guard_msgs in
#roadmap_goal lowerLoopsCorrect

/--
info: open Solidity.Goals.loweringStudyTarget ← Solidity.Correctness.Lowering.lowerLoops_correct blocked by [Solidity.Goals.lowerLoopsCorrect] plan pa-lowering
-/
#guard_msgs in
#roadmap_goal loweringStudyTarget

/-- The local production contract is exactly the dedicated roadmap goal. -/
example :
    (∀ [FreshNames],
      LowerKernel.Fix lowerList lowerStmt lowerLoop ∧
      (∃ (μL : List RawStmt → Nat) (μS μP : RawStmt → Nat),
        LowerKernel.Contractive μL μS μP) ∧
      LowerKernel.Helpers) = Solidity.Goals.loweringKernelTotal := rfl

example : Solidity.Goals.loweringKernelTotal := Solidity.lowerKernel_total

/--
info: proved Solidity.Goals.loweringKernelTotal ← Solidity.lowerKernel_total plan e2a-lower-total
-/
#guard_msgs in
#roadmap_goal loweringKernelTotal

end Solidity.Goals
