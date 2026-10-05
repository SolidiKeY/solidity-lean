import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived: dangling aliases

`⊢` of each obligation that writes through an alias a `pop` made dangle,
in the order of the source; the replays are what `#solkey_derive? …
pending` (`Frontend/Problems.lean`) prints.  The write lands in the slot
past the array's end (`LStor.stale`, KeY's plain `save` at the slot
`storageIndexReadArrayBindLocalRoot` bound), and a later `push()` makes the
slot live again (`LStor.slotU`, `storagePushLengthSaveReferenceElement`
then `selectOnSaveCons`), directly, after a `delete` of the emptied array
(`selectStDelNodeIndexStruct`) or after a copy over it
(`selectOnSaveEmptyIndexStruct`).
-/

open Solidity Proves

theorem Solkey.TestSuite.testDanglingReferenceSurvivesPush.proved :
    ⊢ Solkey.TestSuite.testDanglingReferenceSurvivesPush.problem := by
  sol_prove

theorem Solkey.TestSuite.testArrayCopyKeepsDestinationTail.proved :
    ⊢ Solkey.TestSuite.testArrayCopyKeepsDestinationTail.problem := by
  sol_prove

theorem Solkey.TestSuite.testDeleteArrayLeavesDataPastLength.proved :
    ⊢ Solkey.TestSuite.testDeleteArrayLeavesDataPastLength.problem := by
  sol_prove
