import Solidity.Frontend.Problems
import Solidity.Tools.Counterexample

/-!
# SolKey's open dangling-storage suite

The pinned upstream suite preserves four historical resurrection specifications.
The resetting-push model refutes each at the initial typed state. These kernel
certificates are model counterexamples; Solidity dangling aliases remain
undefined or compiler-specific. No failed search is used as a refutation.
-/

solc_import "../../tests/solc/StorageDanglingOpen.ast.json" hash 0xac9d92a9a35281be
  as Solkey.StorageDanglingOpen
solc_scoped_problems Solkey.StorageDanglingOpen decl

namespace Solidity.Counterexamples.StorageDangling

/-- `delete tokens; ... r.value = 5; delete tokens; tokens.push();` resets the slot. -/
theorem delete_refuted :
    ¬ Valid Solkey.StorageDanglingOpen.testDeleteArrayLeavesDataPastLength.problem := by
  apply Fml.not_valid_of_eval3Peel (dom := Tools.poolDom []) [] (State.init Solkey.StorageDanglingOpen)
  decide +kernel

/-- `tokens.pop(); r.value = 5; tokens.push();` does not resurrect `5` in the model. -/
theorem push_refuted :
    ¬ Valid Solkey.StorageDanglingOpen.testDanglingReferenceSurvivesPush.problem := by
  apply Fml.not_valid_of_eval3Peel (dom := Tools.poolDom []) [] (State.init Solkey.StorageDanglingOpen)
  decide +kernel

/-- `tokens = emptyTokens; tokens.push();` does not resurrect the dirty tail. -/
theorem copy_refuted :
    ¬ Valid Solkey.StorageDanglingOpen.testArrayCopyKeepsDestinationTail.problem := by
  apply Fml.not_valid_of_eval3Peel (dom := Tools.poolDom []) [] (State.init Solkey.StorageDanglingOpen)
  decide +kernel

/-- `matrix.pop(); ptr.push(66); matrix.push();` resets the appended row. -/
theorem inner_refuted :
    ¬ Valid Solkey.StorageDanglingOpen.testDanglingInnerArrayReappearsAfterPush.problem := by
  apply Fml.not_valid_of_eval3Peel (dom := Tools.poolDom []) [] (State.init Solkey.StorageDanglingOpen)
  decide +kernel

end Solidity.Counterexamples.StorageDangling
