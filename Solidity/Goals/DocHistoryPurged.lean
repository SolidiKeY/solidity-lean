import Solidity.Tools.Goal

/-! The plan goal `docHistoryPurged` (`g3-history-purge-docs`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Docs.history_purged "g3-history-purge-docs"]
def docHistoryPurged : Prop := Unstated

end Solidity.Goals
