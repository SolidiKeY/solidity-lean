import Solidity.Tools.Goal

/-! The plan goal `controlsOffCriticalPath` (`t2-controls-off-path`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Controls.off_critical_path "t2-controls-off-path"]
def controlsOffCriticalPath : Prop := Unstated

end Solidity.Goals
