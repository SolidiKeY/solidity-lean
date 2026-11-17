import Solidity.Goals.PanicRun

namespace Solidity.Goals

/--
info: proved Solidity.Goals.panicRunOutcomes ← Solidity.Correctness.Panic.run_outcomes plan w3x-panic-outcomes
-/
#guard_msgs in
#roadmap_goal panicRunOutcomes

example : Solidity.Goals.panicRunOutcomes := Solidity.Correctness.Panic.run_outcomes

/--
info: 'Solidity.Correctness.Panic.run_outcomes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Solidity.Correctness.Panic.run_outcomes

end Solidity.Goals
