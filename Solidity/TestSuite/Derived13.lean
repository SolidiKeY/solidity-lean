import Solidity.TestSuite.ScopedProblems

/-!
# solkey's `TestSuite`, derived: dangling aliases

`⊢` of each obligation that writes through an alias a `pop` made dangle,
in the order of the source; the replays are what `#solkey_derive? …
pending` (`Frontend/Problems.lean`) prints.  The write lands in the slot
past the array's end (KeY's plain `save` at the slot
`storageIndexReadArrayBindLocalRoot` bound, at the dangling location
`SLoc.dangling`), and a later `push()` makes the slot live again as it is
(`TVal.extendA`, `storagePushLengthSaveReferenceElement` then
`selectOnSaveCons`), directly, after a `delete` of the emptied array
(`selectStDelNodeIndexStruct`) or after a copy over it
(`selectOnSaveEmptyIndexStruct`).  A push through the alias
(`storagePushValueSave`) lands in the recycled array, whose length is read
off the slot (`findDefinitionSize`).
-/

open Solidity
open scoped Scoped

theorem Solkey.TestSuite.testDanglingReferenceSurvivesPush.proved :
    ⊢ Solkey.TestSuite.testDanglingReferenceSurvivesPush.problem := by
  sol_prove

theorem Solkey.TestSuite.testArrayCopyKeepsDestinationTail.proved :
    ⊢ Solkey.TestSuite.testArrayCopyKeepsDestinationTail.problem := by
  sol_prove

theorem Solkey.TestSuite.testDeleteArrayLeavesDataPastLength.proved :
    ⊢ Solkey.TestSuite.testDeleteArrayLeavesDataPastLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testDanglingInnerArrayReappearsAfterPush.proved :
    ⊢ Solkey.TestSuite.testDanglingInnerArrayReappearsAfterPush.problem := by
  sol_prove

theorem Solkey.TestSuite.testArrayCopyClearsOldElements.proved : ⊢ Solkey.TestSuite.testArrayCopyClearsOldElements.problem := by
  sol_prove
