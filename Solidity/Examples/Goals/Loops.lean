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

end Solidity.Goals
