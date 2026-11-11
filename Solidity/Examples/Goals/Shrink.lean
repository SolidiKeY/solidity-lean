import Solidity.Goals.Shrink

namespace Solidity.Goals

/--
info: open Solidity.Goals.yulLayoutView ← Solidity.Yul.Layout.view_correct plan yv1-yul-layout-view
-/
#guard_msgs in
#roadmap_goal yulLayoutView

/--
info: open Solidity.Goals.loweringBySimulation ← Solidity.Correctness.Lowering.Sim.lowering_producer plan ls3-lowering-compose
-/
#guard_msgs in
#roadmap_goal loweringBySimulation

end Solidity.Goals
