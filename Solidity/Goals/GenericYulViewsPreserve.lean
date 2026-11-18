import Solidity.Tools.Goal

/-! The plan goal `genericYulViewsPreserve` (`t1-yul-views-generic`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Yul.Views.generic_views_preserve "t1-yul-views-generic"]
def genericYulViewsPreserve : Prop := Unstated

end Solidity.Goals
