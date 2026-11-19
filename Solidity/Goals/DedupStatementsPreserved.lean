import Solidity.Tools.Goal

/-! The plan goal `dedupStatementsPreserved` (`t3-dedup-rollout`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Dedup.statements_preserved "t3-dedup-rollout"]
def dedupStatementsPreserved : Prop := Unstated

end Solidity.Goals
