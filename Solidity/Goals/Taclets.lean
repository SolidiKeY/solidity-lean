import Solidity.Tools.Goal
import Solidity.Calculus.RuleShapes

/-! Finish-line component 6: calculus coverage, `Solidity.RuleShapes.taclets_partitioned`. -/

namespace Solidity.Goals

open Solidity.Goal

open RuleShapes in
@[goal Solidity.RuleShapes.taclets_partitioned]
def tacletsPartitioned : Prop :=
  KeyTaclet.all.all (fun t =>
    (if claims t then (1 : Nat) else 0) +
    (if unclaimedTaclets.contains t then 1 else 0) +
    (if migrationPendingTaclets.contains t then 1 else 0) == 1) = true

end Solidity.Goals
