import Solidity.Goals.Shrink
import Solidity.Yul.Layout.Pilot

namespace Solidity.Goals

/--
info: proved Solidity.Goals.yulLayoutPilot ← Solidity.Yul.Layout.pilot_correct plan yv1-yul-layout-view
-/
#guard_msgs in
#roadmap_goal yulLayoutPilot

/-- The pin's proof closes the goal statement. -/
example : yulLayoutPilot := Solidity.Yul.Layout.pilot_correct

end Solidity.Goals
