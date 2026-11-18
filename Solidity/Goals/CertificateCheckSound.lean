import Solidity.Tools.Goal

/-! The plan goal `certificateCheckSound` (`vu3-certificates`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Automation.Certificate.check_sound "vu3-certificates"]
def certificateCheckSound : Prop := Unstated

end Solidity.Goals
