import Solidity.Tools.Goal

/-! The plan goal `fastModeAgrees` (`vu2-fast-mode`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Automation.fast_mode_agrees "vu2-fast-mode"]
def fastModeAgrees : Prop := Unstated

end Solidity.Goals
