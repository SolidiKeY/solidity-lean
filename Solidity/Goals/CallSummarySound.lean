import Solidity.Tools.Goal

/-! The plan goal `callSummarySound` (`vu4-modular`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Automation.Summary.call_summary_sound "vu4-modular"]
def callSummarySound : Prop := Unstated

end Solidity.Goals
