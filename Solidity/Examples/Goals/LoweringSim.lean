import Solidity.Goals.LoweringSim

namespace Solidity.Goals

/--
info: open Solidity.Goals.loweringBySimulation ← Solidity.Correctness.Lowering.Sim.lowering_producer plan ls3-lowering-compose
-/
#guard_msgs in
#roadmap_goal loweringBySimulation

example : Solidity.Goals.loweringBySimulation =
    (letI : FreshNames := Solidity.Goals.Shrink.Lowering.productionNames;
      Solidity.Goals.Shrink.Lowering.CallerBound ∧
        ∃ D : Solidity.Goals.Shrink.Lowering.Diagram, D.Simulates ∧ D.Total) := rfl

end Solidity.Goals
