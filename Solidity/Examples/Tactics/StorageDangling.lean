import Solidity.Frontend.Problems

/-!
# SolKey's dangling-storage suite

solkey's `solc/StorageDangling.sol` (an open suite at `048a74de51`, a
positive one since `d85018517f`): an empty `push()` saves only the length
(`storagePushLengthSave`), so what a popped alias wrote past the end is
exposed again, as solc's code leaves it.  Each obligation holds in every
state, derived by `sol_prove`.  These executions are compiler-specific;
Solidity leaves a dangling storage alias undefined.  The fixture is the
pinned open suite, the same functions without their comments.
-/

solc_import "../../../tests/solc/StorageDanglingOpen.ast.json" hash 0xac9d92a9a35281be
  as Solkey.StorageDanglingOpen
solc_scoped_problems Solkey.StorageDanglingOpen decl

namespace Solidity.Examples.Tactics.StorageDangling

open Solidity

/-- `delete tokens; … r.value = 5; delete tokens; tokens.push();` exposes `5`. -/
theorem delete_survives :
    Proves Solkey.StorageDanglingOpen .all [] .nil Solkey.StorageDanglingOpen.testDeleteArrayLeavesDataPastLength.problem := by
  sol_prove (steps := 128)

/-- `tokens.pop(); r.value = 5; tokens.push();` exposes `5`. -/
theorem push_survives :
    Proves Solkey.StorageDanglingOpen .all [] .nil Solkey.StorageDanglingOpen.testDanglingReferenceSurvivesPush.problem := by
  sol_prove (steps := 128)

/-- `tokens = emptyTokens; tokens.push();` exposes the dirty tail. -/
theorem copy_survives :
    Proves Solkey.StorageDanglingOpen .all [] .nil Solkey.StorageDanglingOpen.testArrayCopyKeepsDestinationTail.problem := by
  sol_prove (steps := 128)

/-- `matrix.pop(); ptr.push(66); matrix.push();` exposes the inner row. -/
theorem inner_survives :
    Proves Solkey.StorageDanglingOpen .all [] .nil Solkey.StorageDanglingOpen.testDanglingInnerArrayReappearsAfterPush.problem := by
  sol_prove (steps := 128)

end Solidity.Examples.Tactics.StorageDangling
