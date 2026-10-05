import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived: dangling aliases

`⊢` of each obligation that writes through an alias a `pop` made dangle,
in the order of the source; the replays are what `#solkey_derive? …
pending` (`Frontend/Problems.lean`) prints.  The write lands in the slot
past the array's end (`LStor.stale`, KeY's plain `save` at the slot
`storageIndexReadArrayBindLocalRoot` bound), and a later `push()` makes the
slot live again (`LStor.slotU`, `storagePushLengthSaveReferenceElement`
then `selectOnSaveCons`).
-/

open Solidity Proves

theorem Solkey.TestSuite.testDanglingReferenceSurvivesPush.proved :
    ⊢ Solkey.TestSuite.testDanglingReferenceSurvivesPush.problem := by
  sol_prove
